theory "TwoInputs"
  imports Complex_Main
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

(* 2.Two inputs component with properties *)
(* (trait TwoInputs) *)

datatype ('t1,'t2) TwoInputsTrait =
  Tuple_of2 (Compute2 : "'t1 Signal \<times> 't1 Signal \<Rightarrow> 't2 Signal") 
            (Latency2 : nat)
            (Reliability2 : real)

(* Delay = latency of f + max of latencies on the inputs *)
fun global_delay :: 
   "nat \<Rightarrow> 'a Signal \<times> 'a Signal \<Rightarrow> nat" where
   "global_delay n_f (x,y) = n_f + (max (latency x) (latency y))" 

(* Reliability for a parallel composition of 2^k identical modules *)
fun reliabilityParal :: "real \<Rightarrow> nat \<Rightarrow> real" where
  "reliabilityParal R k = 1 - (1-R)^(2^k)"

lemma reliabilityParal_lem1 :
  "reliabilityParal R (k+1) = (reliabilityParal R k) * (1 + (1-R)^(2^k))"
  apply (auto)
  by (smt (verit, best) mult.commute mult_2 mult_minus_left power_add square_diff_one_factored)

lemma reliabilityParal_lem2 :
  "reliabilityParal (Reliability2 c) (k+1) = 
           (reliabilityParal (Reliability2 c) k) * (1 + (1-(Reliability2 c))^(2^k))"
  using reliabilityParal_lem1 by auto

(* 3.Combinational adder and multiplier *)

fun fadd_simple :: "nat Signal \<times> nat Signal \<Rightarrow> nat Signal" where
   "fadd_simple (x,y) = Wire ((signal_value x) + (signal_value y))"

fun add_simple :: "real \<Rightarrow> (nat, nat) TwoInputsTrait" where
  "add_simple r = (Tuple_of2 fadd_simple 0 r)"

fun fmul_simple :: "nat Signal \<times> nat Signal \<Rightarrow> nat Signal" where
   "fmul_simple (x,y) = Wire ((signal_value x) * (signal_value y))"

fun mul_simple :: "real \<Rightarrow> (nat, nat) TwoInputsTrait" where
  "mul_simple r = (Tuple_of2 fmul_simple 0 r)"

(* 4.Adder and multiplier with register on the output *)

fun fadd_reg :: "nat Signal \<times> nat Signal \<Rightarrow> nat Signal" where
  "fadd_reg (x,y) = Reg (Wire ((signal_value x) + (signal_value y)))"

fun add_reg :: "real \<Rightarrow> (nat, nat) TwoInputsTrait" where
  "add_reg r = (Tuple_of2 fadd_reg 1 r)"

fun fmul_reg :: "nat Signal \<times> nat Signal \<Rightarrow> nat Signal" where
   "fmul_reg (x,y) = Reg (Wire ((signal_value x) * (signal_value y)))"

fun mul_reg :: "real \<Rightarrow> (nat, nat) TwoInputsTrait" where
  "mul_reg r = (Tuple_of2 fmul_reg 1 r)"

(* 5.Multiplier for a DSP *)

fun RegEnable :: "'a Signal \<Rightarrow> bool Signal \<Rightarrow> 'a \<Rightarrow> 'a Signal" where
  "RegEnable x enable currval = 
        Reg (Wire (if (signal_value enable) then (signal_value x) else currval))"

primrec ShiftRegister :: "'a Signal \<Rightarrow> nat \<Rightarrow> bool Signal \<Rightarrow> 'a \<Rightarrow> 'a Signal" where
  "ShiftRegister x 0 en init = x" |
  "ShiftRegister x (Suc n) en init = 
       (RegEnable (ShiftRegister x n en (signal_value (RegEnable x en init))) en init)"

fun fmul_DSP :: "nat Signal \<times> nat Signal \<Rightarrow> nat Signal" where
   "fmul_DSP (x,y) = ShiftRegister (Wire ((signal_value x) * (signal_value y))) 3 (Wire True) 0"

fun mul_DSP :: "real \<Rightarrow> (nat, nat) TwoInputsTrait" where
  "mul_DSP r = (Tuple_of2 fmul_DSP 3 r)"

end
