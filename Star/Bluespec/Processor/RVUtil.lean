import Star.Bluespec.Lib.BluespecPrelude
open BluespecPrelude

namespace RVUtil

structure t_instfields where
  opcode : BitVec 7
  funct3 : BitVec 3
  funct7 : BitVec 7
  funct5 : BitVec 5
  funct2 : BitVec 2
  rd : BitVec 5
  rs1 : BitVec 5
  rs2 : BitVec 5
  rs3 : BitVec 5
  immI : BitVec 32
  immS : BitVec 32
  immB : BitVec 32
  immU : BitVec 32
  immJ : BitVec 32
  csr : BitVec 12
deriving Inhabited

structure t_controlresult where
  taken : t_bool
  nextPC : BitVec 32
deriving Inhabited

inductive t_immediatetype where
  | ImmI : unit_ → t_immediatetype
  | ImmS : unit_ → t_immediatetype
  | ImmB : unit_ → t_immediatetype
  | ImmU : unit_ → t_immediatetype
  | ImmJ : unit_ → t_immediatetype
deriving BEq
open t_immediatetype
export t_immediatetype (ImmI ImmS ImmB ImmU ImmJ)
-- OfNat instances for integer comparisons
instance : OfNat t_immediatetype 0 where
  ofNat := ImmI default
instance : OfNat t_immediatetype 1 where
  ofNat := ImmS default
instance : OfNat t_immediatetype 2 where
  ofNat := ImmB default
instance : OfNat t_immediatetype 3 where
  ofNat := ImmU default
instance : OfNat t_immediatetype 4 where
  ofNat := ImmJ default

structure t_decodedinst where
  legal : t_bool
  valid_rs1 : t_bool
  valid_rs2 : t_bool
  valid_rd : t_bool
  immediateType : t_maybe t_immediatetype
  inst : BitVec 32
deriving Inhabited

def default_instfields : t_instfields := { opcode := 0, funct3 := 0, funct7 := 0, funct5 := 0, funct2 := 0, rd := 0, rs1 := 0, rs2 := 0, rs3 := 0, immI := 0, immS := 0, immB := 0, immU := 0, immJ := 0, csr := 0 }
instance : Inhabited t_instfields where
  default := { opcode := 0, funct3 := 0, funct7 := 0, funct5 := 0, funct2 := 0, rd := 0, rs1 := 0, rs2 := 0, rs3 := 0, immI := 0, immS := 0, immB := 0, immU := 0, immJ := 0, csr := 0 }

def default_controlresult : t_controlresult := { taken := BFalse Unit_, nextPC := 0 }
instance : Inhabited t_controlresult where
  default := { taken := BFalse Unit_, nextPC := 0 }

def default_immediatetype : t_immediatetype := ImmI Unit_
instance : Inhabited t_immediatetype where
  default := ImmI Unit_

def default_decodedinst : t_decodedinst := { legal := BFalse Unit_, valid_rs1 := BFalse Unit_, valid_rs2 := BFalse Unit_, valid_rd := BFalse Unit_, immediateType := Invalid Unit_, inst := 0 }
instance : Inhabited t_decodedinst where
  default := { legal := BFalse Unit_, valid_rs1 := BFalse Unit_, valid_rs2 := BFalse Unit_, valid_rd := BFalse Unit_, immediateType := Invalid Unit_, inst := 0 }

def getInstFields : BitVec 32 → t_instfields :=
  fun (inst : BitVec 32) =>
    { opcode := extract_bits inst 6 0, funct3 := extract_bits inst 14 12, funct7 := extract_bits inst 31 25, funct5 := extract_bits inst 31 27, funct2 := extract_bits inst 26 25, rd := extract_bits inst 11 7, rs1 := extract_bits inst 19 15, rs2 := extract_bits inst 24 20, rs3 := extract_bits inst 31 27, immI := sign_extend (extract_bits inst 31 20), immS := sign_extend (concat_bits (extract_bits inst 31 25) 5 (extract_bits inst 11 7)), immB := sign_extend (concat_bits (extract_bits inst 31 31) 12 (concat_bits (extract_bits inst 7 7) 11 (concat_bits (extract_bits inst 30 25) 5 (concat_bits (extract_bits inst 11 8) 1 (0 : BitVec 1))))), immU := sign_extend (concat_bits (extract_bits inst 31 12) 12 (0 : BitVec 12)), immJ := sign_extend (concat_bits (extract_bits inst 31 31) 20 (concat_bits (extract_bits inst 19 12) 12 (concat_bits (extract_bits inst 20 20) 11 (concat_bits (extract_bits inst 30 21) 1 (0 : BitVec 1))))), csr := extract_bits inst 31 20 }

def isMemoryInst : t_decodedinst → t_bool :=
  fun (dInst : t_decodedinst) =>
    bool_and (if ((extract_bits dInst.inst 6 6 == (0 : BitVec 1)))
                then BTrue Unit_
                else BFalse Unit_) (if ((extract_bits dInst.inst 4 3 == (0 : BitVec 2)))
                                      then BTrue Unit_
                                      else BFalse Unit_)

def isControlInst : t_decodedinst → t_bool :=
  fun (dInst : t_decodedinst) =>
    if ((extract_bits dInst.inst 6 4 == (6 : BitVec 3)))
      then BTrue Unit_
      else BFalse Unit_

def usesRS1 : BitVec 32 → t_bool :=
  fun (inst : BitVec 32) =>
    match _ : (if ((extract_bits inst 6 2 == (24 : BitVec 5)))
                 then BTrue Unit_
                 else BFalse Unit_) with
      | BTrue _ => BTrue Unit_
      | BFalse _ => match _ : (if ((extract_bits inst 6 2 == (0 : BitVec 5)))
                                 then BTrue Unit_
                                 else BFalse Unit_) with
                      | BTrue _ => BTrue Unit_
                      | BFalse _ => match _ : (if ((extract_bits inst 6 2 == (8 : BitVec 5)))
                                                 then BTrue Unit_
                                                 else BFalse Unit_) with
                                      | BTrue _ => BTrue Unit_
                                      | BFalse _ => match _ : (if ((extract_bits inst 6 2 == (12 : BitVec 5)))
                                                                 then BTrue Unit_
                                                                 else BFalse Unit_) with
                                                      | BTrue _ => BTrue Unit_
                                                      | BFalse _ => match _ : (if ((extract_bits inst 6 2 == (25 : BitVec 5)))
                                                                                 then BTrue Unit_
                                                                                 else BFalse Unit_) with
                                                                      | BTrue _ => BTrue Unit_
                                                                      | BFalse _ => if ((extract_bits inst 6 2 == (4 : BitVec 5)))
                                                                                      then BTrue Unit_
                                                                                      else BFalse Unit_

def usesRS2 : BitVec 32 → t_bool :=
  fun (inst : BitVec 32) =>
    match _ : (if ((extract_bits inst 6 2 == (24 : BitVec 5)))
                 then BTrue Unit_
                 else BFalse Unit_) with
      | BTrue _ => BTrue Unit_
      | BFalse _ => match _ : (if ((extract_bits inst 6 2 == (8 : BitVec 5)))
                                 then BTrue Unit_
                                 else BFalse Unit_) with
                      | BTrue _ => BTrue Unit_
                      | BFalse _ => if ((extract_bits inst 6 2 == (12 : BitVec 5)))
                                      then BTrue Unit_
                                      else BFalse Unit_

def usesRD : BitVec 32 → t_bool :=
  fun (inst : BitVec 32) =>
    match _ : (if ((extract_bits inst 6 2 == (13 : BitVec 5)))
                 then BTrue Unit_
                 else BFalse Unit_) with
      | BTrue _ => BTrue Unit_
      | BFalse _ => match _ : (if ((extract_bits inst 6 2 == (27 : BitVec 5)))
                                 then BTrue Unit_
                                 else BFalse Unit_) with
                      | BTrue _ => BTrue Unit_
                      | BFalse _ => match _ : (if ((extract_bits inst 6 2 == (0 : BitVec 5)))
                                                 then BTrue Unit_
                                                 else BFalse Unit_) with
                                      | BTrue _ => BTrue Unit_
                                      | BFalse _ => match _ : (if ((extract_bits inst 6 2 == (12 : BitVec 5)))
                                                                 then BTrue Unit_
                                                                 else BFalse Unit_) with
                                                      | BTrue _ => BTrue Unit_
                                                      | BFalse _ => match _ : (if ((extract_bits inst 6 2 == (25 : BitVec 5)))
                                                                                 then BTrue Unit_
                                                                                 else BFalse Unit_) with
                                                                      | BTrue _ => BTrue Unit_
                                                                      | BFalse _ => match _ : (if ((extract_bits inst 6 2 == (4 : BitVec 5)))
                                                                                                 then BTrue Unit_
                                                                                                 else BFalse Unit_) with
                                                                                      | BTrue _ => BTrue Unit_
                                                                                      | BFalse _ => if ((extract_bits inst 6 2 == (5 : BitVec 5)))
                                                                                                      then BTrue Unit_
                                                                                                      else BFalse Unit_

def getImmediateI : BitVec 32 → BitVec 32 :=
    fun (inst : BitVec 32) =>
      sign_extend (extract_bits inst 31 20)

def getImmediateS : BitVec 32 → BitVec 32 :=
    fun (inst : BitVec 32) =>
      sign_extend (concat_bits (extract_bits inst 31 25) 5 (extract_bits inst 11 7))

def getImmediateB : BitVec 32 → BitVec 32 :=
    fun (inst : BitVec 32) =>
      sign_extend (concat_bits (extract_bits inst 31 31) 12 (concat_bits (extract_bits inst 7 7) 11 (concat_bits (extract_bits inst 30 25) 5 (concat_bits (extract_bits inst 11 8) 1 (0 : BitVec 1)))))

def getImmediateU : BitVec 32 → BitVec 32 :=
    fun (inst : BitVec 32) =>
      sign_extend (concat_bits (extract_bits inst 31 12) 12 (0 : BitVec 12))

def getImmediateJ : BitVec 32 → BitVec 32 :=
    fun (inst : BitVec 32) =>
      sign_extend (concat_bits (extract_bits inst 31 31) 20 (concat_bits (extract_bits inst 19 12) 12 (concat_bits (extract_bits inst 20 20) 11 (concat_bits (extract_bits inst 30 21) 1 (0 : BitVec 1)))))

def fn3_BEQ : BitVec 3 :=
  (0 : BitVec 3)

def fn3_BNE : BitVec 3 :=
  (1 : BitVec 3)

def fn3_BLT : BitVec 3 :=
  (4 : BitVec 3)

def fn3_BGE : BitVec 3 :=
  (5 : BitVec 3)

def fn3_BLTU : BitVec 3 :=
  (6 : BitVec 3)

def fn3_BGEU : BitVec 3 :=
  (7 : BitVec 3)

def fn3_ADDSUB : BitVec 3 :=
  (0 : BitVec 3)

def op5_LOAD : BitVec 5 :=
  (0 : BitVec 5)

def op5_LOADFP : BitVec 5 :=
  (1 : BitVec 5)

def op5_OPIMM : BitVec 5 :=
  (4 : BitVec 5)

def op5_OPIMM32 : BitVec 5 :=
  (6 : BitVec 5)

def op5_JALR : BitVec 5 :=
  (25 : BitVec 5)

def op5_AUIPC : BitVec 5 :=
  (5 : BitVec 5)

def op5_LUI : BitVec 5 :=
  (13 : BitVec 5)

def op5_STORE : BitVec 5 :=
  (8 : BitVec 5)

def op5_STOREFP : BitVec 5 :=
  (9 : BitVec 5)

def op5_BRANCH : BitVec 5 :=
  (24 : BitVec 5)

def op5_JAL : BitVec 5 :=
  (27 : BitVec 5)

def op_LOAD : BitVec 7 :=
  (3 : BitVec 7)

def fn3_B : BitVec 3 :=
  (0 : BitVec 3)

def fn3_H : BitVec 3 :=
  (1 : BitVec 3)

def fn3_W : BitVec 3 :=
  (2 : BitVec 3)

def fn3_BU : BitVec 3 :=
  (4 : BitVec 3)

def fn3_HU : BitVec 3 :=
  (5 : BitVec 3)

def op_OPIMM : BitVec 7 :=
  (19 : BitVec 7)

def fn3_SLT : BitVec 3 :=
  (2 : BitVec 3)

def fn3_SLTU : BitVec 3 :=
  (3 : BitVec 3)

def fn3_XOR : BitVec 3 :=
  (4 : BitVec 3)

def fn3_OR : BitVec 3 :=
  (6 : BitVec 3)

def fn3_AND : BitVec 3 :=
  (7 : BitVec 3)

def fn3_SLL : BitVec 3 :=
  (1 : BitVec 3)

def fn3_SR : BitVec 3 :=
  (5 : BitVec 3)

def op_AUIPC : BitVec 7 :=
  (23 : BitVec 7)

def op_STORE : BitVec 7 :=
  (35 : BitVec 7)

def op_OP : BitVec 7 :=
  (51 : BitVec 7)

def fn3_DIV : BitVec 3 :=
  (4 : BitVec 3)

def fn3_DIVU : BitVec 3 :=
  (5 : BitVec 3)

def fn3_REM : BitVec 3 :=
  (6 : BitVec 3)

def fn3_REMU : BitVec 3 :=
  (7 : BitVec 3)

def op_LUI : BitVec 7 :=
  (55 : BitVec 7)

def op_BRANCH : BitVec 7 :=
  (99 : BitVec 7)

def op_JALR : BitVec 7 :=
  (103 : BitVec 7)

def op_JAL : BitVec 7 :=
  (111 : BitVec 7)

def op_SYSTEM : BitVec 7 :=
  (115 : BitVec 7)

def fn3_PRIV : BitVec 3 :=
  (0 : BitVec 3)

def fn3_MUL : BitVec 3 :=
  (0 : BitVec 3)

def getImmediate : t_decodedinst → BitVec 32 :=
  fun (dInst : t_decodedinst) =>
    match _ : (if ((dInst.immediateType == Valid (ImmI Unit_)))
                 then BTrue Unit_
                 else BFalse Unit_) with
      | BTrue _ => getImmediateI dInst.inst
      | BFalse _ => match _ : (if ((dInst.immediateType == Valid (ImmS Unit_)))
                                 then BTrue Unit_
                                 else BFalse Unit_) with
                      | BTrue _ => getImmediateS dInst.inst
                      | BFalse _ => match _ : (if ((dInst.immediateType == Valid (ImmB Unit_)))
                                                 then BTrue Unit_
                                                 else BFalse Unit_) with
                                      | BTrue _ => getImmediateB dInst.inst
                                      | BFalse _ => match _ : (if ((dInst.immediateType == Valid (ImmU Unit_)))
                                                                 then BTrue Unit_
                                                                 else BFalse Unit_) with
                                                      | BTrue _ => getImmediateU dInst.inst
                                                      | BFalse _ => match _ : (if ((dInst.immediateType == Valid (ImmJ Unit_)))
                                                                                 then BTrue Unit_
                                                                                 else BFalse Unit_) with
                                                                      | BTrue _ => getImmediateJ dInst.inst
                                                                      | BFalse _ => 0

def execControl32 : BitVec 32 → BitVec 32 → BitVec 32 → BitVec 32 → BitVec 32 → t_controlresult :=
  fun (inst : BitVec 32) =>
    fun (rs1_val : BitVec 32) =>
      fun (rs2_val : BitVec 32) =>
        fun (imm_val : BitVec 32) =>
          fun (pc : BitVec 32) =>
            let incPC : BitVec 32 := (pc + 4)
            let funct3 : BitVec 3 := extract_bits inst 14 12
            let taken : t_bool := BTrue Unit_
            let nextPC : BitVec 32 := incPC
            let _theResult__ : t_primpair (BitVec 32) t_bool := match _ : (bitvec1_to_bool (bit_not (bool_to_bitvec1 (if ((extract_bits inst 6 4 == (6 : BitVec 3)))
                                                                                                                        then BTrue Unit_
                                                                                                                        else BFalse Unit_)))) with
                                                                  | BTrue _ => let _theResult__ : t_primpair (BitVec 32) t_bool := tuple2 incPC (BFalse Unit_)
                                                                               tuple2 _theResult__.fst _theResult__.snd
                                                                  | BFalse _ => let _theResult__ : t_primpair (BitVec 32) t_bool := match _ : (bitvec1_to_bool (bool_to_bitvec1 (bitvec1_to_bool (bit_and (bool_to_bitvec1 (if ((extract_bits inst 2 2 == (1 : BitVec 1)))
                                                                                                                                                                                                                              then BTrue Unit_
                                                                                                                                                                                                                              else BFalse Unit_)) (bool_to_bitvec1 (if ((extract_bits inst 3 3 == (1 : BitVec 1)))
                                                                                                                                                                                                                                                                      then BTrue Unit_
                                                                                                                                                                                                                                                                      else BFalse Unit_)))))) with
                                                                                                                                      | BTrue _ => let _theResult__ : t_primpair (BitVec 32) t_bool := tuple2 (pc + imm_val) (BTrue Unit_)
                                                                                                                                                   tuple2 _theResult__.fst _theResult__.snd
                                                                                                                                      | BFalse _ => let _theResult__ : t_primpair (BitVec 32) t_bool := match _ : (bitvec1_to_bool (bool_to_bitvec1 (bitvec1_to_bool (bit_and (bool_to_bitvec1 (if ((extract_bits inst 2 2 == (1 : BitVec 1)))
                                                                                                                                                                                                                                                                                                  then BTrue Unit_
                                                                                                                                                                                                                                                                                                  else BFalse Unit_)) (bool_to_bitvec1 (if ((extract_bits inst 3 3 == (0 : BitVec 1)))
                                                                                                                                                                                                                                                                                                                                          then BTrue Unit_
                                                                                                                                                                                                                                                                                                                                          else BFalse Unit_)))))) with
                                                                                                                                                                                                          | BTrue _ => let _theResult__ : t_primpair (BitVec 32) t_bool := tuple2 (bit_and (rs1_val + imm_val) (bit_not 1)) (BTrue Unit_)
                                                                                                                                                                                                                       tuple2 _theResult__.fst _theResult__.snd
                                                                                                                                                                                                          | BFalse _ => let _theResult__ : t_primpair (BitVec 32) t_bool := let taken : t_bool := match _ : (if ((funct3 == fn3_BEQ))
                                                                                                                                                                                                                                                                                                               then BTrue Unit_
                                                                                                                                                                                                                                                                                                               else BFalse Unit_) with
                                                                                                                                                                                                                                                                                                    | BTrue _ => if ((rs1_val == rs2_val))
                                                                                                                                                                                                                                                                                                                   then BTrue Unit_
                                                                                                                                                                                                                                                                                                                   else BFalse Unit_
                                                                                                                                                                                                                                                                                                    | BFalse _ => match _ : (if ((funct3 == fn3_BNE))
                                                                                                                                                                                                                                                                                                                               then BTrue Unit_
                                                                                                                                                                                                                                                                                                                               else BFalse Unit_) with
                                                                                                                                                                                                                                                                                                                    | BTrue _ => if ((rs1_val != rs2_val))
                                                                                                                                                                                                                                                                                                                                   then BTrue Unit_
                                                                                                                                                                                                                                                                                                                                   else BFalse Unit_
                                                                                                                                                                                                                                                                                                                    | BFalse _ => match _ : (if ((funct3 == fn3_BLT))
                                                                                                                                                                                                                                                                                                                                               then BTrue Unit_
                                                                                                                                                                                                                                                                                                                                               else BFalse Unit_) with
                                                                                                                                                                                                                                                                                                                                    | BTrue _ => if ((rs1_val < rs2_val))
                                                                                                                                                                                                                                                                                                                                                   then BTrue Unit_
                                                                                                                                                                                                                                                                                                                                                   else BFalse Unit_
                                                                                                                                                                                                                                                                                                                                    | BFalse _ => match _ : (if ((funct3 == fn3_BGE))
                                                                                                                                                                                                                                                                                                                                                               then BTrue Unit_
                                                                                                                                                                                                                                                                                                                                                               else BFalse Unit_) with
                                                                                                                                                                                                                                                                                                                                                    | BTrue _ => bool_not (if ((rs1_val < rs2_val))
                                                                                                                                                                                                                                                                                                                                                                             then BTrue Unit_
                                                                                                                                                                                                                                                                                                                                                                             else BFalse Unit_)
                                                                                                                                                                                                                                                                                                                                                    | BFalse _ => match _ : (if ((funct3 == fn3_BLTU))
                                                                                                                                                                                                                                                                                                                                                                               then BTrue Unit_
                                                                                                                                                                                                                                                                                                                                                                               else BFalse Unit_) with
                                                                                                                                                                                                                                                                                                                                                                    | BTrue _ => if ((rs1_val < rs2_val))
                                                                                                                                                                                                                                                                                                                                                                                   then BTrue Unit_
                                                                                                                                                                                                                                                                                                                                                                                   else BFalse Unit_
                                                                                                                                                                                                                                                                                                                                                                    | BFalse _ => match _ : (if ((funct3 == fn3_BGEU))
                                                                                                                                                                                                                                                                                                                                                                                               then BTrue Unit_
                                                                                                                                                                                                                                                                                                                                                                                               else BFalse Unit_) with
                                                                                                                                                                                                                                                                                                                                                                                    | BTrue _ => if ((rs1_val >= rs2_val))
                                                                                                                                                                                                                                                                                                                                                                                                   then BTrue Unit_
                                                                                                                                                                                                                                                                                                                                                                                                   else BFalse Unit_
                                                                                                                                                                                                                                                                                                                                                                                    | BFalse _ => default
                                                                                                                                                                                                                                                                            tuple2 (match _ : (bitvec1_to_bool (bool_to_bitvec1 taken)) with
                                                                                                                                                                                                                                                                                      | BTrue _ => (pc + imm_val)
                                                                                                                                                                                                                                                                                      | BFalse _ => incPC) taken
                                                                                                                                                                                                                        tuple2 _theResult__.fst _theResult__.snd
                                                                                                                                                    tuple2 _theResult__.fst _theResult__.snd
                                                                                tuple2 _theResult__.fst _theResult__.snd
            { taken := _theResult__.snd, nextPC := _theResult__.fst }

def getImmediateTypeFrom32BitInst : BitVec 32 → t_maybe t_immediatetype :=
  fun (inst : BitVec 32) =>
    match _ : (bitvec1_to_bool (bit_or (bit_or (bit_or (bit_or (bool_to_bitvec1 (if ((extract_bits inst 6 2 == op5_LOAD))
                                                                                   then BTrue Unit_
                                                                                   else BFalse Unit_)) (bool_to_bitvec1 (if ((extract_bits inst 6 2 == op5_LOADFP))
                                                                                                                           then BTrue Unit_
                                                                                                                           else BFalse Unit_))) (bool_to_bitvec1 (if ((extract_bits inst 6 2 == op5_OPIMM))
                                                                                                                                                                    then BTrue Unit_
                                                                                                                                                                    else BFalse Unit_))) (bool_to_bitvec1 (if ((extract_bits inst 6 2 == op5_OPIMM32))
                                                                                                                                                                                                             then BTrue Unit_
                                                                                                                                                                                                             else BFalse Unit_))) (bool_to_bitvec1 (if ((extract_bits inst 6 2 == op5_JALR))
                                                                                                                                                                                                                                                      then BTrue Unit_
                                                                                                                                                                                                                                                      else BFalse Unit_)))) with
      | BTrue _ => Valid (ImmI Unit_)
      | BFalse _ => match _ : (bitvec1_to_bool (bit_or (bool_to_bitvec1 (if ((extract_bits inst 6 2 == op5_AUIPC))
                                                                           then BTrue Unit_
                                                                           else BFalse Unit_)) (bool_to_bitvec1 (if ((extract_bits inst 6 2 == op5_LUI))
                                                                                                                   then BTrue Unit_
                                                                                                                   else BFalse Unit_)))) with
                      | BTrue _ => Valid (ImmU Unit_)
                      | BFalse _ => match _ : (bitvec1_to_bool (bit_or (bool_to_bitvec1 (if ((extract_bits inst 6 2 == op5_STORE))
                                                                                           then BTrue Unit_
                                                                                           else BFalse Unit_)) (bool_to_bitvec1 (if ((extract_bits inst 6 2 == op5_STOREFP))
                                                                                                                                   then BTrue Unit_
                                                                                                                                   else BFalse Unit_)))) with
                                      | BTrue _ => Valid (ImmS Unit_)
                                      | BFalse _ => match _ : (if ((extract_bits inst 6 2 == op5_BRANCH))
                                                                 then BTrue Unit_
                                                                 else BFalse Unit_) with
                                                      | BTrue _ => Valid (ImmB Unit_)
                                                      | BFalse _ => match _ : (if ((extract_bits inst 6 2 == op5_JAL))
                                                                                 then BTrue Unit_
                                                                                 else BFalse Unit_) with
                                                                      | BTrue _ => Valid (ImmJ Unit_)
                                                                      | BFalse _ => Invalid Unit_

def alu32 : BitVec 3 → BitVec 1 → BitVec 32 → BitVec 32 → BitVec 32 :=
  fun (funct3 : BitVec 3) =>
    fun (inst_30 : BitVec 1) =>
      fun (a : BitVec 32) =>
        fun (b : BitVec 32) =>
          let shamt : BitVec 5 := truncate b 5
          match _ : (if ((funct3 == fn3_ADDSUB))
                       then BTrue Unit_
                       else BFalse Unit_) with
            | BTrue _ => match _ : (bitvec1_to_bool (bool_to_bitvec1 (if ((inst_30 == (1 : BitVec 1)))
                                                                        then BTrue Unit_
                                                                        else BFalse Unit_))) with
                           | BTrue _ => (a - b)
                           | BFalse _ => (a + b)
            | BFalse _ => match _ : (if ((funct3 == fn3_SLL))
                                       then BTrue Unit_
                                       else BFalse Unit_) with
                            | BTrue _ => shift_left a shamt
                            | BFalse _ => match _ : (if ((funct3 == fn3_SLT))
                                                       then BTrue Unit_
                                                       else BFalse Unit_) with
                                            | BTrue _ => zero_extend (bool_to_bitvec1 (if ((a < b))
                                                                                         then BTrue Unit_
                                                                                         else BFalse Unit_)) 32
                                            | BFalse _ => match _ : (if ((funct3 == fn3_SLTU))
                                                                       then BTrue Unit_
                                                                       else BFalse Unit_) with
                                                            | BTrue _ => zero_extend (bool_to_bitvec1 (if ((a < b))
                                                                                                         then BTrue Unit_
                                                                                                         else BFalse Unit_)) 32
                                                            | BFalse _ => match _ : (if ((funct3 == fn3_XOR))
                                                                                       then BTrue Unit_
                                                                                       else BFalse Unit_) with
                                                                            | BTrue _ => bit_xor a b
                                                                            | BFalse _ => match _ : (if ((funct3 == fn3_SR))
                                                                                                       then BTrue Unit_
                                                                                                       else BFalse Unit_) with
                                                                                            | BTrue _ => match _ : (bitvec1_to_bool (bool_to_bitvec1 (if ((inst_30 == (1 : BitVec 1)))
                                                                                                                                                        then BTrue Unit_
                                                                                                                                                        else BFalse Unit_))) with
                                                                                                           | BTrue _ => shift_right_arith a shamt
                                                                                                           | BFalse _ => shift_right_logical a shamt
                                                                                            | BFalse _ => match _ : (if ((funct3 == fn3_OR))
                                                                                                                       then BTrue Unit_
                                                                                                                       else BFalse Unit_) with
                                                                                                            | BTrue _ => bit_or a b
                                                                                                            | BFalse _ => match _ : (if ((funct3 == fn3_AND))
                                                                                                                                       then BTrue Unit_
                                                                                                                                       else BFalse Unit_) with
                                                                                                                            | BTrue _ => bit_and a b
                                                                                                                            | BFalse _ => 0

def isMultiplyInst : BitVec 32 → t_bool :=
  fun (inst : BitVec 32) =>
    let fields : t_instfields := getInstFields inst
    bitvec1_to_bool (bit_and (bit_and (bool_to_bitvec1 (if ((fields.funct7 == (1 : BitVec 7)))
                                                          then BTrue Unit_
                                                          else BFalse Unit_)) (bool_to_bitvec1 (if ((fields.funct3 == fn3_MUL))
                                                                                                  then BTrue Unit_
                                                                                                  else BFalse Unit_))) (bool_to_bitvec1 (if ((fields.opcode == op_OP))
                                                                                                                                           then BTrue Unit_
                                                                                                                                           else BFalse Unit_)))

def execALU32 : BitVec 32 → BitVec 32 → BitVec 32 → BitVec 32 → BitVec 32 → BitVec 32 :=
  fun (inst : BitVec 32) =>
    fun (rs1_val : BitVec 32) =>
      fun (rs2_val : BitVec 32) =>
        fun (imm_val : BitVec 32) =>
          fun (pc : BitVec 32) =>
            let isIMM : t_bool := if ((extract_bits inst 5 5 == (0 : BitVec 1)))
                                    then BTrue Unit_
                                    else BFalse Unit_
            let rd_val : BitVec 32 := 0
            match _ : (bitvec1_to_bool (bool_to_bitvec1 (bitvec1_to_bool (bit_and (bool_to_bitvec1 (if ((extract_bits inst 2 2 == (1 : BitVec 1)))
                                                                                                      then BTrue Unit_
                                                                                                      else BFalse Unit_)) (bool_to_bitvec1 (if ((extract_bits inst 5 5 == (1 : BitVec 1)))
                                                                                                                                              then BTrue Unit_
                                                                                                                                              else BFalse Unit_)))))) with
              | BTrue _ => imm_val
              | BFalse _ => match _ : (bitvec1_to_bool (bool_to_bitvec1 (bitvec1_to_bool (bit_and (bool_to_bitvec1 (if ((extract_bits inst 2 2 == (1 : BitVec 1)))
                                                                                                                      then BTrue Unit_
                                                                                                                      else BFalse Unit_)) (bool_to_bitvec1 (if ((extract_bits inst 5 5 == (0 : BitVec 1)))
                                                                                                                                                              then BTrue Unit_
                                                                                                                                                              else BFalse Unit_)))))) with
                              | BTrue _ => (pc + imm_val)
                              | BFalse _ => let funct3 : BitVec 3 := extract_bits inst 14 12
                                            alu32 funct3 (match _ : (bitvec1_to_bool (bit_and (bool_to_bitvec1 (if ((funct3 == fn3_ADDSUB))
                                                                                                                  then BTrue Unit_
                                                                                                                  else BFalse Unit_)) (bool_to_bitvec1 isIMM))) with
                                                            | BTrue _ => 0
                                                            | BFalse _ => extract_bits inst 30 30) rs1_val (match _ : (bitvec1_to_bool (bool_to_bitvec1 isIMM)) with
                                                                                                              | BTrue _ => imm_val
                                                                                                              | BFalse _ => rs2_val)

def isLegalInstruction : BitVec 32 → t_bool :=
  fun (inst : BitVec 32) =>
    let fields : t_instfields := getInstFields inst
    bitvec1_to_bool (bit_or (bool_to_bitvec1 (match _ : (if ((fields.opcode == op_LOAD))
                                                           then BTrue Unit_
                                                           else BFalse Unit_) with
                                                | BTrue _ => bitvec1_to_bool (bit_or (bit_or (bit_or (bit_or (bool_to_bitvec1 (if ((fields.funct3 == fn3_B))
                                                                                                                                 then BTrue Unit_
                                                                                                                                 else BFalse Unit_)) (bool_to_bitvec1 (if ((fields.funct3 == fn3_H))
                                                                                                                                                                         then BTrue Unit_
                                                                                                                                                                         else BFalse Unit_))) (bool_to_bitvec1 (if ((fields.funct3 == fn3_W))
                                                                                                                                                                                                                  then BTrue Unit_
                                                                                                                                                                                                                  else BFalse Unit_))) (bool_to_bitvec1 (if ((fields.funct3 == fn3_BU))
                                                                                                                                                                                                                                                           then BTrue Unit_
                                                                                                                                                                                                                                                           else BFalse Unit_))) (bool_to_bitvec1 (if ((fields.funct3 == fn3_HU))
                                                                                                                                                                                                                                                                                                    then BTrue Unit_
                                                                                                                                                                                                                                                                                                    else BFalse Unit_)))
                                                | BFalse _ => match _ : (if ((fields.opcode == op_OPIMM))
                                                                           then BTrue Unit_
                                                                           else BFalse Unit_) with
                                                                | BTrue _ => match _ : (bitvec1_to_bool (bit_or (bit_or (bit_or (bit_or (bit_or (bool_to_bitvec1 (if ((fields.funct3 == fn3_ADDSUB))
                                                                                                                                                                    then BTrue Unit_
                                                                                                                                                                    else BFalse Unit_)) (bool_to_bitvec1 (if ((fields.funct3 == fn3_SLT))
                                                                                                                                                                                                            then BTrue Unit_
                                                                                                                                                                                                            else BFalse Unit_))) (bool_to_bitvec1 (if ((fields.funct3 == fn3_SLTU))
                                                                                                                                                                                                                                                     then BTrue Unit_
                                                                                                                                                                                                                                                     else BFalse Unit_))) (bool_to_bitvec1 (if ((fields.funct3 == fn3_XOR))
                                                                                                                                                                                                                                                                                              then BTrue Unit_
                                                                                                                                                                                                                                                                                              else BFalse Unit_))) (bool_to_bitvec1 (if ((fields.funct3 == fn3_OR))
                                                                                                                                                                                                                                                                                                                                       then BTrue Unit_
                                                                                                                                                                                                                                                                                                                                       else BFalse Unit_))) (bool_to_bitvec1 (if ((fields.funct3 == fn3_AND))
                                                                                                                                                                                                                                                                                                                                                                                then BTrue Unit_
                                                                                                                                                                                                                                                                                                                                                                                else BFalse Unit_)))) with
                                                                               | BTrue _ => BTrue Unit_
                                                                               | BFalse _ => match _ : (if ((fields.funct3 == fn3_SLL))
                                                                                                          then BTrue Unit_
                                                                                                          else BFalse Unit_) with
                                                                                               | BTrue _ => bitvec1_to_bool (bit_and (bool_to_bitvec1 (if ((extract_bits fields.funct7 6 1 == (0 : BitVec 6)))
                                                                                                                                                         then BTrue Unit_
                                                                                                                                                         else BFalse Unit_)) (bool_to_bitvec1 (if ((extract_bits fields.funct7 0 0 == (0 : BitVec 1)))
                                                                                                                                                                                                 then BTrue Unit_
                                                                                                                                                                                                 else BFalse Unit_)))
                                                                                               | BFalse _ => match _ : (if ((fields.funct3 == fn3_SR))
                                                                                                                          then BTrue Unit_
                                                                                                                          else BFalse Unit_) with
                                                                                                               | BTrue _ => bitvec1_to_bool (bit_and (bit_or (bool_to_bitvec1 (if ((extract_bits fields.funct7 6 1 == (0 : BitVec 6)))
                                                                                                                                                                                 then BTrue Unit_
                                                                                                                                                                                 else BFalse Unit_)) (bool_to_bitvec1 (if ((extract_bits fields.funct7 6 1 == (16 : BitVec 6)))
                                                                                                                                                                                                                         then BTrue Unit_
                                                                                                                                                                                                                         else BFalse Unit_))) (bool_to_bitvec1 (if ((extract_bits fields.funct7 0 0 == (0 : BitVec 1)))
                                                                                                                                                                                                                                                                  then BTrue Unit_
                                                                                                                                                                                                                                                                  else BFalse Unit_)))
                                                                                                               | BFalse _ => BFalse Unit_
                                                                | BFalse _ => match _ : (if ((fields.opcode == op_AUIPC))
                                                                                           then BTrue Unit_
                                                                                           else BFalse Unit_) with
                                                                                | BTrue _ => BTrue Unit_
                                                                                | BFalse _ => match _ : (if ((fields.opcode == op_STORE))
                                                                                                           then BTrue Unit_
                                                                                                           else BFalse Unit_) with
                                                                                                | BTrue _ => bitvec1_to_bool (bit_or (bit_or (bool_to_bitvec1 (if ((fields.funct3 == fn3_B))
                                                                                                                                                                 then BTrue Unit_
                                                                                                                                                                 else BFalse Unit_)) (bool_to_bitvec1 (if ((fields.funct3 == fn3_H))
                                                                                                                                                                                                         then BTrue Unit_
                                                                                                                                                                                                         else BFalse Unit_))) (bool_to_bitvec1 (if ((fields.funct3 == fn3_W))
                                                                                                                                                                                                                                                  then BTrue Unit_
                                                                                                                                                                                                                                                  else BFalse Unit_)))
                                                                                                | BFalse _ => match _ : (if ((fields.opcode == op_OP))
                                                                                                                           then BTrue Unit_
                                                                                                                           else BFalse Unit_) with
                                                                                                                | BTrue _ => match _ : (bitvec1_to_bool (bit_or (bool_to_bitvec1 (if ((fields.funct3 == fn3_ADDSUB))
                                                                                                                                                                                    then BTrue Unit_
                                                                                                                                                                                    else BFalse Unit_)) (bool_to_bitvec1 (if ((fields.funct3 == fn3_SR))
                                                                                                                                                                                                                            then BTrue Unit_
                                                                                                                                                                                                                            else BFalse Unit_)))) with
                                                                                                                               | BTrue _ => bitvec1_to_bool (bit_or (bool_to_bitvec1 (if ((fields.funct7 == (0 : BitVec 7)))
                                                                                                                                                                                        then BTrue Unit_
                                                                                                                                                                                        else BFalse Unit_)) (bool_to_bitvec1 (if ((fields.funct7 == (32 : BitVec 7)))
                                                                                                                                                                                                                                then BTrue Unit_
                                                                                                                                                                                                                                else BFalse Unit_)))
                                                                                                                               | BFalse _ => match _ : (bitvec1_to_bool (bit_or (bit_or (bit_or (bit_or (bit_or (bit_or (bit_or (bit_or (bit_or (bool_to_bitvec1 (if ((fields.funct3 == fn3_DIV))
                                                                                                                                                                                                                                                                    then BTrue Unit_
                                                                                                                                                                                                                                                                    else BFalse Unit_)) (bool_to_bitvec1 (if ((fields.funct3 == fn3_DIVU))
                                                                                                                                                                                                                                                                                                            then BTrue Unit_
                                                                                                                                                                                                                                                                                                            else BFalse Unit_))) (bool_to_bitvec1 (if ((fields.funct3 == fn3_REM))
                                                                                                                                                                                                                                                                                                                                                     then BTrue Unit_
                                                                                                                                                                                                                                                                                                                                                     else BFalse Unit_))) (bool_to_bitvec1 (if ((fields.funct3 == fn3_REMU))
                                                                                                                                                                                                                                                                                                                                                                                              then BTrue Unit_
                                                                                                                                                                                                                                                                                                                                                                                              else BFalse Unit_))) (bool_to_bitvec1 (if ((fields.funct3 == fn3_SLL))
                                                                                                                                                                                                                                                                                                                                                                                                                                       then BTrue Unit_
                                                                                                                                                                                                                                                                                                                                                                                                                                       else BFalse Unit_))) (bool_to_bitvec1 (if ((fields.funct3 == fn3_SLT))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                then BTrue Unit_
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                else BFalse Unit_))) (bool_to_bitvec1 (if ((fields.funct3 == fn3_SLTU))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         then BTrue Unit_
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         else BFalse Unit_))) (bool_to_bitvec1 (if ((fields.funct3 == fn3_XOR))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  then BTrue Unit_
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  else BFalse Unit_))) (bool_to_bitvec1 (if ((fields.funct3 == fn3_OR))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           then BTrue Unit_
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           else BFalse Unit_))) (bool_to_bitvec1 (if ((fields.funct3 == fn3_AND))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    then BTrue Unit_
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    else BFalse Unit_)))) with
                                                                                                                                               | BTrue _ => if ((fields.funct7 == (0 : BitVec 7)))
                                                                                                                                                              then BTrue Unit_
                                                                                                                                                              else BFalse Unit_
                                                                                                                                               | BFalse _ => BFalse Unit_
                                                                                                                | BFalse _ => match _ : (if ((fields.opcode == op_LUI))
                                                                                                                                           then BTrue Unit_
                                                                                                                                           else BFalse Unit_) with
                                                                                                                                | BTrue _ => BTrue Unit_
                                                                                                                                | BFalse _ => match _ : (if ((fields.opcode == op_BRANCH))
                                                                                                                                                           then BTrue Unit_
                                                                                                                                                           else BFalse Unit_) with
                                                                                                                                                | BTrue _ => bitvec1_to_bool (bit_or (bit_or (bit_or (bit_or (bit_or (bool_to_bitvec1 (if ((fields.funct3 == fn3_BEQ))
                                                                                                                                                                                                                                         then BTrue Unit_
                                                                                                                                                                                                                                         else BFalse Unit_)) (bool_to_bitvec1 (if ((fields.funct3 == fn3_BNE))
                                                                                                                                                                                                                                                                                 then BTrue Unit_
                                                                                                                                                                                                                                                                                 else BFalse Unit_))) (bool_to_bitvec1 (if ((fields.funct3 == fn3_BLT))
                                                                                                                                                                                                                                                                                                                          then BTrue Unit_
                                                                                                                                                                                                                                                                                                                          else BFalse Unit_))) (bool_to_bitvec1 (if ((fields.funct3 == fn3_BGE))
                                                                                                                                                                                                                                                                                                                                                                   then BTrue Unit_
                                                                                                                                                                                                                                                                                                                                                                   else BFalse Unit_))) (bool_to_bitvec1 (if ((fields.funct3 == fn3_BLTU))
                                                                                                                                                                                                                                                                                                                                                                                                            then BTrue Unit_
                                                                                                                                                                                                                                                                                                                                                                                                            else BFalse Unit_))) (bool_to_bitvec1 (if ((fields.funct3 == fn3_BGEU))
                                                                                                                                                                                                                                                                                                                                                                                                                                                     then BTrue Unit_
                                                                                                                                                                                                                                                                                                                                                                                                                                                     else BFalse Unit_)))
                                                                                                                                                | BFalse _ => match _ : (if ((fields.opcode == op_JALR))
                                                                                                                                                                           then BTrue Unit_
                                                                                                                                                                           else BFalse Unit_) with
                                                                                                                                                                | BTrue _ => if ((fields.funct3 == (0 : BitVec 3)))
                                                                                                                                                                               then BTrue Unit_
                                                                                                                                                                               else BFalse Unit_
                                                                                                                                                                | BFalse _ => match _ : (if ((fields.opcode == op_JAL))
                                                                                                                                                                                           then BTrue Unit_
                                                                                                                                                                                           else BFalse Unit_) with
                                                                                                                                                                                | BTrue _ => BTrue Unit_
                                                                                                                                                                                | BFalse _ => match _ : (if ((fields.opcode == op_SYSTEM))
                                                                                                                                                                                                           then BTrue Unit_
                                                                                                                                                                                                           else BFalse Unit_) with
                                                                                                                                                                                                | BTrue _ => match _ : (if ((fields.funct3 == fn3_PRIV))
                                                                                                                                                                                                                          then BTrue Unit_
                                                                                                                                                                                                                          else BFalse Unit_) with
                                                                                                                                                                                                               | BTrue _ => bitvec1_to_bool (bit_and (bool_to_bitvec1 (if ((fields.rd == (0 : BitVec 5)))
                                                                                                                                                                                                                                                                         then BTrue Unit_
                                                                                                                                                                                                                                                                         else BFalse Unit_)) (bool_to_bitvec1 (match _ : (if ((concat_bits fields.funct7 5 fields.rs2 == (0 : BitVec 12)))
                                                                                                                                                                                                                                                                                                                            then BTrue Unit_
                                                                                                                                                                                                                                                                                                                            else BFalse Unit_) with
                                                                                                                                                                                                                                                                                                                 | BTrue _ => if ((fields.rs1 == (0 : BitVec 5)))
                                                                                                                                                                                                                                                                                                                                then BTrue Unit_
                                                                                                                                                                                                                                                                                                                                else BFalse Unit_
                                                                                                                                                                                                                                                                                                                 | BFalse _ => match _ : (if ((concat_bits fields.funct7 5 fields.rs2 == (1 : BitVec 12)))
                                                                                                                                                                                                                                                                                                                                            then BTrue Unit_
                                                                                                                                                                                                                                                                                                                                            else BFalse Unit_) with
                                                                                                                                                                                                                                                                                                                                 | BTrue _ => if ((fields.rs1 == (0 : BitVec 5)))
                                                                                                                                                                                                                                                                                                                                                then BTrue Unit_
                                                                                                                                                                                                                                                                                                                                                else BFalse Unit_
                                                                                                                                                                                                                                                                                                                                 | BFalse _ => match _ : (if ((concat_bits fields.funct7 5 fields.rs2 == (770 : BitVec 12)))
                                                                                                                                                                                                                                                                                                                                                            then BTrue Unit_
                                                                                                                                                                                                                                                                                                                                                            else BFalse Unit_) with
                                                                                                                                                                                                                                                                                                                                                 | BTrue _ => if ((fields.rs1 == (0 : BitVec 5)))
                                                                                                                                                                                                                                                                                                                                                                then BTrue Unit_
                                                                                                                                                                                                                                                                                                                                                                else BFalse Unit_
                                                                                                                                                                                                                                                                                                                                                 | BFalse _ => match _ : (if ((concat_bits fields.funct7 5 fields.rs2 == (261 : BitVec 12)))
                                                                                                                                                                                                                                                                                                                                                                            then BTrue Unit_
                                                                                                                                                                                                                                                                                                                                                                            else BFalse Unit_) with
                                                                                                                                                                                                                                                                                                                                                                 | BTrue _ => if ((fields.rs1 == (0 : BitVec 5)))
                                                                                                                                                                                                                                                                                                                                                                                then BTrue Unit_
                                                                                                                                                                                                                                                                                                                                                                                else BFalse Unit_
                                                                                                                                                                                                                                                                                                                                                                 | BFalse _ => BFalse Unit_)))
                                                                                                                                                                                                               | BFalse _ => BFalse Unit_
                                                                                                                                                                                                | BFalse _ => BFalse Unit_)) (bool_to_bitvec1 (isMultiplyInst inst)))

def decodeInst : BitVec 32 → t_decodedinst :=
  fun (input_inst : BitVec 32) =>
    let inst : BitVec 32 := input_inst
    { legal := isLegalInstruction input_inst, valid_rs1 := usesRS1 inst, valid_rs2 := usesRS2 inst, valid_rd := usesRD inst, immediateType := getImmediateTypeFrom32BitInst inst, inst := inst }
