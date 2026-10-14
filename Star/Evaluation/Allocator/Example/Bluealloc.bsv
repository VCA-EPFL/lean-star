import Memory::*;
import FIFO::*;
import FIFOF::*;

typedef Bit#(16) PtrStable;
typedef Bit#(16) PtrUnstable;
typedef Bit#(32) Data;

typedef enum {
  OP_IDLE,
  OP_READ_INDEX,   // waiting for bram_index response (read path)
  OP_READ_DATA,    // waiting for bram_data response (read path)
  OP_WRITE_INDEX,  // waiting for bram_index response (write path)
  OP_FREE_LOOKUP,  // waiting for bram_index response (free path)
  OP_FREE_READ,    // waiting for bram_data + bram_rever responses
  OP_FREE_WRITE    // performing the swap writes
} OpState deriving (Bits, Eq, FShow);

typedef enum {
  AL_PREFETCH,  // need to send bram_rever read request
  AL_WAIT,      // waiting for bram_rever response
  AL_READY      // pre-fetched stable ptr available
} AllocState deriving (Bits, Eq, FShow);

interface Bluealloc;
  method ActionValue#(PtrStable) alloc();
  method Action free(PtrStable f);
  method Action write_req(PtrStable addr, Data data);
  method Action read_req(PtrStable addr);
  method ActionValue#(Data) read_resp();
endinterface

module mkBluealloc(Bluealloc);
  // Data storage, indexed by unstable pointers
  SimpleBRAM2#(PtrUnstable, Data)      bram_data  <- mkSimpleBRAM2;
  // Stable -> Unstable mapping (the indirection layer)
  SimpleBRAM2#(PtrStable, PtrUnstable) bram_index <- mkSimpleBRAM2;
  // Unstable -> Stable reverse mapping (for compaction on free)
  SimpleBRAM2#(PtrUnstable, PtrStable) bram_rever <- mkSimpleBRAM2;

  // Entries [0, enqPtr) in unstable space are allocated
  Reg#(PtrUnstable) enqPtr <- mkReg(0);

  // High-water mark: slots [0, maxEver) have identity mappings in BRAM
  Reg#(PtrUnstable) maxEver <- mkReg(0);

  // ---- Operation state machine (read / write / free) ----
  Reg#(OpState) opState <- mkReg(OP_IDLE);

  // Holding registers for multi-cycle operations
  Reg#(Data)        opWriteData      <- mkRegU;  // data to write (write path)
  Reg#(PtrStable)   freeStableAddr   <- mkRegU;  // stable addr being freed
  Reg#(PtrUnstable) freeUnstableAddr <- mkRegU;  // its unstable counterpart
  Reg#(PtrStable)   freeLastStable   <- mkRegU;  // stable ptr at last allocated slot
  Reg#(Data)        freeDataAtAddr   <- mkRegU;  // data at freed slot
  Reg#(Data)        freeDataAtLast   <- mkRegU;  // data at last allocated slot

  // -- Read path: index lookup -> data lookup --
  rule do_read_index (opState == OP_READ_INDEX);
    let unstable <- bram_index.readA();
    bram_data.putA(False, unstable, ?);
    opState <= OP_READ_DATA;
  endrule

  // -- Write path: index lookup -> data write --
  rule do_write_index (opState == OP_WRITE_INDEX);
    let unstable <- bram_index.readA();
    bram_data.putA(True, unstable, opWriteData);
    opState <= OP_IDLE;
  endrule

  // -- Free path: 3-step FSM --
  // Step 1: got addr_unstable, now read both data slots + reverse at last slot
  rule do_free_lookup (opState == OP_FREE_LOOKUP);
    let unstable <- bram_index.readA();
    freeUnstableAddr <= unstable;
    let lastUnstable = enqPtr - 1;
    // Read data at both positions (use both ports of bram_data)
    bram_data.putA(False, unstable, ?);
    bram_data.putB(False, lastUnstable, ?);
    // Read stable ptr at last allocated position
    bram_rever.putA(False, lastUnstable, ?);
    opState <= OP_FREE_READ;
  endrule

  // Step 2: collect all responses
  rule do_free_read (opState == OP_FREE_READ);
    let dAddr <- bram_data.readA();
    let dLast <- bram_data.readB();
    let sLast <- bram_rever.readA();
    freeDataAtAddr <= dAddr;
    freeDataAtLast <= dLast;
    freeLastStable <= sLast;
    opState <= OP_FREE_WRITE;
  endrule

  // Step 3: perform the swap and update all mappings
  rule do_free_write (opState == OP_FREE_WRITE);
    let lastUnstable = enqPtr - 1;
    // Swap data between freed slot and last allocated slot
    bram_data.putA(True, freeUnstableAddr, freeDataAtLast);
    bram_data.putB(True, lastUnstable, freeDataAtAddr);
    // Update reverse mapping
    bram_rever.putA(True, freeUnstableAddr, freeLastStable);
    bram_rever.putB(True, lastUnstable, freeStableAddr);
    // Update index mapping
    bram_index.putA(True, freeLastStable, freeUnstableAddr);
    bram_index.putB(True, freeStableAddr, lastUnstable);
    // Shrink allocated region
    enqPtr <= lastUnstable;
    opState <= OP_IDLE;
  endrule

  Reg#(AllocState) allocState <- mkReg(AL_PREFETCH);
  Reg#(PtrStable)  allocNextStable <- mkRegU;

  rule do_alloc_prefetch (allocState == AL_PREFETCH && opState == OP_IDLE);
    if (enqPtr >= maxEver) begin
      // Fresh slot: identity mapping, no BRAM read needed
      allocNextStable <= enqPtr;
      allocState <= AL_READY;
    end else begin
      // Recycled slot: must read reverse mapping from BRAM
      bram_rever.putB(False, enqPtr, ?);
      allocState <= AL_WAIT;
    end
  endrule

  rule do_alloc_wait (allocState == AL_WAIT);
    let s <- bram_rever.readB();
    allocNextStable <= s;
    allocState <= AL_READY;
  endrule


  method ActionValue#(PtrStable) alloc()
      if (allocState == AL_READY && enqPtr < 65535 && opState == OP_IDLE);
    if (enqPtr >= maxEver) begin
      // Fresh slot: write identity mappings to BRAM
      bram_index.putB(True, enqPtr, enqPtr);
      bram_rever.putB(True, enqPtr, enqPtr);
      maxEver <= enqPtr + 1;
    end
    enqPtr <= enqPtr + 1;
    allocState <= AL_PREFETCH;
    return allocNextStable;
  endmethod

  method Action free(PtrStable addr)
      if (opState == OP_IDLE && allocState == AL_READY && enqPtr > 0);
    freeStableAddr <= addr;
    // Kick off free FSM: look up the unstable ptr for this stable addr
    bram_index.putA(False, addr, ?);
    opState <= OP_FREE_LOOKUP;
    allocState <= AL_PREFETCH;  // invalidate, enqPtr will change
  endmethod

  method Action write_req(PtrStable addr, Data data)
      if (opState == OP_IDLE);
    opWriteData <= data;
    bram_index.putA(False, addr, ?);
    opState <= OP_WRITE_INDEX;
  endmethod

  method Action read_req(PtrStable addr)
      if (opState == OP_IDLE);
    bram_index.putA(False, addr, ?);
    opState <= OP_READ_INDEX;
  endmethod

  method ActionValue#(Data) read_resp() if (opState == OP_READ_DATA);
    let d <- bram_data.readA();
    opState <= OP_IDLE;
    return d;
  endmethod

endmodule
