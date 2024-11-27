theory "chisel_types"
  imports Main
begin 

(* 1.Simple model for signals *)
(* Wire : wire (internal signal or primary input/output), 
   Reg : output of a flip-flop *)
datatype 'a Signal = 
  Wire 'a |
  Reg "'a Signal" 

primrec signal_value :: "'a Signal \<Rightarrow> 'a" where
   "signal_value (Wire x) = x" |
   "signal_value (Reg x) =  signal_value x" 

primrec latency :: "'a Signal \<Rightarrow> nat" where
   "latency (Wire x) = 0" |
   "latency (Reg x) =  (latency x) + 1" 

(* 2.RegEnable *)
(* https://www.chisel-lang.org/api/latest/chisel3/util/RegEnable$.html *)
fun RegEnable :: "'a Signal \<Rightarrow> bool Signal \<Rightarrow> 'a \<Rightarrow> 'a Signal" where
  "RegEnable x enable currval = 
        Reg (Wire (if (signal_value enable) then (signal_value x) else currval))"

fun globallatency_RegEnable :: "'a Signal \<Rightarrow> bool Signal \<Rightarrow> nat" where
  "globallatency_RegEnable x enable = (max (latency x) (latency enable)) + 1"

(* 3.ShiftRegister *)
(* https://javadoc.io/doc/edu.berkeley.cs/chisel3_2.12/3.2.1/chisel3/util/ShiftRegister$.html *)

primrec ShiftRegister :: "'a Signal \<Rightarrow> nat \<Rightarrow> bool Signal \<Rightarrow> 'a \<Rightarrow> 'a Signal" where
  "ShiftRegister x 0 en init = x" |
  "ShiftRegister x (Suc n) en init = 
       (RegEnable (ShiftRegister x n en (signal_value (RegEnable x en init))) en init)"

primrec latency_ShiftRegister :: "'a Signal \<Rightarrow> nat \<Rightarrow> bool Signal \<Rightarrow> nat" where
  "latency_ShiftRegister x 0 en = (max (latency x) (latency en))" |
  "latency_ShiftRegister x (Suc n) en = 
               (max (latency_ShiftRegister x n en) (latency en)) + 1"

lemma latency_shiftregister_k :
  "latency_ShiftRegister (Wire x) k (Wire en) = k"
  apply (induct k)
  apply (auto)
  done

(* 4.Pipe of k stages *)
(* https://www.chisel-lang.org/api/latest/chisel3/util/Pipe$.html,
   https://github.com/chipsalliance/chisel/blob/main/src/main/scala/chisel3/util/Valid.scala *) 

datatype 'a Valid_type =
   Pair_valid_bits (Valid : "bool Signal") 
                   (Bits : "'a Signal")

primrec pipe_apply :: "bool Signal \<Rightarrow> 'a Signal \<Rightarrow> 'a \<Rightarrow> nat 
                       \<Rightarrow> ('a Valid_type) Signal" where
  "pipe_apply enable x init 0 = Wire (Pair_valid_bits enable x)" |
  "pipe_apply enable x init (Suc k) = 
        pipe_apply (Reg enable) (RegEnable x enable init) 
                   (signal_value (RegEnable x enable init)) k"

primrec latency_pipe_apply :: "bool Signal \<Rightarrow> 'a Signal \<Rightarrow> nat \<Rightarrow> nat" where
  "latency_pipe_apply enable x 0 = max (latency enable) (latency x)" |
  "latency_pipe_apply enable x (Suc k) =
            (latency_pipe_apply enable x k) + (globallatency_RegEnable x enable)"

lemma lem_latency_pipe :
  "latency_pipe_apply (Wire enable) (Wire x) n = n"
  apply (induct n)
  apply (auto)
  done

fun pipe_apply_valid_type :: "('a Valid_type) Signal  \<Rightarrow> 'a \<Rightarrow> nat 
                              \<Rightarrow> ('a Valid_type) Signal" where
   "pipe_apply_valid_type s i k = pipe_apply (Valid (signal_value s))
                                             (Bits (signal_value s)) i k"

fun latency_pipe_apply_valid_type :: "('a Valid_type) Signal \<Rightarrow> nat \<Rightarrow> nat" where
   "latency_pipe_apply_valid_type s k = 
          latency_pipe_apply (Valid (signal_value s))
                             (Bits (signal_value s)) k"

lemma lem_latency_pipe_valid_type :
  "latency_pipe_apply_valid_type (Wire (Pair_valid_bits (Wire enable) (Wire x))) n = n"
  apply (auto)
  by (simp add: lem_latency_pipe)

end
