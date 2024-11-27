theory "ParameterizedDotProduct"
  imports Complex_Main
begin 

(* 1.Simple model for signals *)
(* Wire : wire (internal signal or primary input/output), 
   Reg : output of a flip-flop *)
datatype 't Signal = 
  Wire 't |
  Reg "'t Signal" 

primrec signal_value :: "'t Signal \<Rightarrow> 't" where
   "signal_value (Wire x) = x" |
   "signal_value (Reg x) =  signal_value x" 

primrec latency :: "'t Signal \<Rightarrow> nat" where
   "latency (Wire x) = 0" |
   "latency (Reg x) =  (latency x) + 1" 

(* 2.Two inputs component with properties (trait TwoInputs) *)

datatype ('t1,'t2) TwoInputsTrait =
  Tuple_of2 (Compute2 : "'t1 Signal \<times> 't1 Signal \<Rightarrow> 't2 Signal") 
            (Latency2 : nat)
            (Reliability2 : real)

(* Delay = latency of f + max of latencies on the inputs *)
fun global_delay :: 
   "nat \<Rightarrow> 'a Signal \<times> 'a Signal \<Rightarrow> nat" where
   "global_delay n_f (x,y) = n_f + (max (latency x) (latency y))" 

(* 3.Tree of two-input components (Chisel reduceTree) *)

fun grouped2 :: "'a Signal list \<Rightarrow> ('a Signal \<times> 'a Signal) list" where
   "grouped2 [] = []" |
   "grouped2 (x#[]) = []" |
   "grouped2 (x#(y#ys)) = ((x,y)#(grouped2 ys))"

lemma length_grouped2_1 :
  "length (grouped2 (a#b#l)) = 1 + (length (grouped2 l))"
  apply (induct l)
  apply (auto)
  done

lemma length_grouped2_2 :
  "length (grouped2 (a#l)) = 
      (if (even (length l)) then (length (grouped2 l)) 
                            else (1 + (length (grouped2 l))))"
  apply (induct l)
  apply (auto)
  apply (metis (no_types, opaque_lifting) Suc_eq_plus1 length_Suc_conv length_grouped2_1 oddE)
  by (smt (verit, best) grouped2.elims length_grouped2_1 list.sel(3))

lemma length_grouped2_decreases [termination_simp] :
  "length(grouped2 (a#b#l)) < (length (a#b#l))"
  apply (induct l)
  apply (auto)
  by (simp add: length_grouped2_2)

function recReduce :: "('t Signal \<times> 't Signal \<Rightarrow> 't Signal) 
                      \<Rightarrow>'t Signal list 
                      \<Rightarrow> 't Signal list" where
   "recReduce f [] = []" |  
   "recReduce f (x#[]) = []" |
   "recReduce f (x#(y#[])) = [f(x,y)]" |
   "recReduce f (x#(y#z#ys)) = 
            recReduce f (map f (grouped2 (x#(y#z#ys))))"
  by pat_completeness auto 
termination recReduce
  apply (relation "measure(\<lambda>(f,l).length(map f (grouped2 l)))")
  apply (auto)
  by (metis (no_types, lifting) One_nat_def Suc_eq_plus1 antisym_conv3 grouped2.elims length_greater_0_conv length_grouped2_decreases length_map less_zeroE list.discI list.size(4))

fun reduceTree :: 
    "('t Signal \<times> 't Signal \<Rightarrow> 't Signal) \<Rightarrow> 't Signal list \<Rightarrow> 't Signal list"  where
  "reduceTree f l = recReduce f l"

(* Latency for a tree with input vectors v1 and v2, where both 
   (length v1) and (length v2) equal (power 2 log2len_v)     *)
fun latencyTree :: "('t,'t) TwoInputsTrait \<Rightarrow> nat \<Rightarrow> nat"
  where
   "latencyTree m log2len_v = log2len_v * (Latency2 m)"

(* Reliability for a parallel composition of 2^k identical modules *)
fun reliabilityParal :: "real \<Rightarrow> nat \<Rightarrow> real" where
  "reliabilityParal R k = 1 - (1-R)^(2^k)"

lemma reliabilityParal_lem1 :
  "reliabilityParal R (k+1) = (reliabilityParal R k) * (1 + (1-R)^(2^k))"
  apply (auto)
  by (smt (verit, best) mult.commute mult_2 mult_minus_left power_add square_diff_one_factored)

(* Reliability for a tree of n stages *)
fun reliabilityTree :: "real \<Rightarrow> nat \<Rightarrow> real" where
  "reliabilityTree R 0 = 1" |
  "reliabilityTree R n = (reliabilityTree R (n-1)) * (reliabilityParal R n)"

(* 4.Dot product generator, as a TwoInputs component *)
(* Expressed in a functional way, using the Map-Reduce pattern *)

datatype 't CoreprodType =
  Tuple_ofT (Compute : "'t Signal list \<Rightarrow> 't Signal list  \<Rightarrow> 't Signal")
            (Latency : nat)
            (Reliability : real)

fun computeCoreDotProduct :: 
    "('t,'t) TwoInputsTrait \<Rightarrow>  ('t,'t) TwoInputsTrait
     \<Rightarrow> 't Signal list \<Rightarrow> 't Signal list \<Rightarrow> 't Signal"  where
   "computeCoreDotProduct mul add l1 l2 =
         (hd (reduceTree (Compute2 add) (map (Compute2 mul) (zip l1 l2))))"

fun computeDotProduct :: 
    "('t,'t) TwoInputsTrait \<Rightarrow>  ('t,'t) TwoInputsTrait
     \<Rightarrow> 't Signal list \<Rightarrow> 't Signal list \<Rightarrow> 't Signal"  where
   "computeDotProduct mul add l1 l2 =
         (Reg (computeCoreDotProduct mul add (map Reg l1) (map Reg l2)))"

(* Latency: *)

fun latencyCoreDotProduct :: 
   "('t,'t) TwoInputsTrait \<Rightarrow> ('t,'t) TwoInputsTrait \<Rightarrow> nat \<Rightarrow> nat"
  where
   "latencyCoreDotProduct mul add log2len_v =
         (Latency2 mul) + (latencyTree add log2len_v)"

fun the_max :: "nat list \<Rightarrow> nat" where
  "the_max [] = 0" |
  "the_max (x#l) = (max x (the_max l))"

fun global_latencyCoreDotProduct :: 
   "('t,'t) TwoInputsTrait \<Rightarrow> ('t,'t) TwoInputsTrait 
    \<Rightarrow> 't Signal list \<Rightarrow> 't Signal list \<Rightarrow> nat \<Rightarrow> nat"
  where
   "global_latencyCoreDotProduct mul add v1 v2 log2len_v =
      (latencyCoreDotProduct mul add log2len_v) +
      (the_max ((map latency v1)@(map latency v2)))"
(* where both (length v1) and (length v2) equal (power 2 log2len_v) *)

fun global_latencyDotProduct :: 
   "('t,'t) TwoInputsTrait \<Rightarrow> ('t,'t) TwoInputsTrait 
    \<Rightarrow> 't Signal list \<Rightarrow> 't Signal list \<Rightarrow> nat \<Rightarrow> nat"
  where
   "global_latencyDotProduct mul add v1 v2 log2len_v =
      (latencyCoreDotProduct mul add log2len_v) +
      (the_max ((map latency (map Reg v1))@(map latency (map Reg v2)))) + 1"
(* where both (length v1) and (length v2) equal (power 2 log2len_v) *)

(* Reliability: *)

fun reliabilityCoreDotProduct ::
  "('t,'t) TwoInputsTrait \<Rightarrow>  ('t,'t) TwoInputsTrait \<Rightarrow> nat \<Rightarrow> real"
  where
  "reliabilityCoreDotProduct mul add k = 
       (reliabilityParal (Reliability2 mul) k) 
       * (reliabilityTree (Reliability2 add) (k-1))"

lemma reliabilityCoreDotProduct_lem1 :
   "k > 0 \<Longrightarrow> 
    reliabilityCoreDotProduct mul add (k+1) =
    (reliabilityParal (Reliability2 mul) k) 
    * (1 + (1- (Reliability2 mul))^(2^k)) 
    * (reliabilityTree (Reliability2 add) (k-1)) 
    * (reliabilityParal (Reliability2 add) k)"
  using reliabilityParal_lem1
  apply (auto)
  by (metis One_nat_def nat_less_le reliabilityParal.elims reliabilityTree.elims)

lemma reliabilityCoreDotProduct_lem2 :
   "k > 0 \<Longrightarrow> 
    reliabilityCoreDotProduct mul add (k+1) =
        (reliabilityCoreDotProduct mul add k) *
        (1 + (1-(Reliability2 mul))^(2^k)) *
        (reliabilityParal (Reliability2 add) k)"
  using reliabilityCoreDotProduct_lem1
  by (smt (verit, best) ab_semigroup_mult_class.mult_ac(1) mult.commute reliabilityCoreDotProduct.simps)

lemma reliabilityCoreDotProduct_kplus1 :
  "(k>0 \<and> ((length v1_1) = (power 2 k)) \<and> ((length v2_1) = (power 2 k)) \<and>
          ((length v1_2) = (power 2 (k+1))) \<and> ((length v2_2) = (power 2 (k+1))))
   \<Longrightarrow>
     Reliability (Tuple_ofT
              (computeCoreDotProduct mul add)
              (global_delay_DotProduct mult add v1_2 v2_2 (k+1))
              (reliabilityCoreDotProduct mul add (k+1)))
    = (Reliability (Tuple_ofT
              (computeCoreDotProduct mul add)
              (global_delay_DotProduct mul add v1_1 v2_1 k)
              (reliabilityCoreDotProduct mul add k)))
      * (1 + (1-(Reliability2 mul))^(2^k)) * (reliabilityParal (Reliability2 add) k)"
  using reliabilityCoreDotProduct_lem2
  by auto

fun reliabilityDotProduct ::
  "('t,'t) TwoInputsTrait \<Rightarrow>  ('t,'t) TwoInputsTrait \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> real"
  where
  "reliabilityDotProduct mul add relreg k = 
       (reliabilityParal relreg (k+1)) * (reliabilityCoreDotProduct mul add k) * relreg"

(* 5.Some properties of the dot product *)

(* Latency for dot product with variants of module mult: *)
(* If m>n, Latency of dotproduct with mult of latency m =
           (Latency of dotproduct with mult of latency n) + m-n *)
lemma latencyDotproduct_mult :
  "(k>0 \<and> ((length v1) = (power 2 k)) \<and> ((length v2) = (power 2 k)) \<and> m>n)
   \<Longrightarrow>
    Latency (Tuple_ofT
              (computeDotProduct (Tuple_of2 mult2 m r2) add)
              (global_latencyDotProduct (Tuple_of2 mult2 m r2) add v1 v2 k)
              (reliabilityDotProduct (Tuple_of2 mult2 m r2) add rr k))
    = (Latency (Tuple_ofT
                 (computeDotProduct (Tuple_of2 mult1 n r1) add)
                 (global_latencyDotProduct (Tuple_of2 mult1 n r1) add v1 v2 k)
                 (reliabilityDotProduct (Tuple_of2  mult1 n r1) add rr k)))
      + (m-n)"
  apply (auto)
  done

(* Latency for dot product with variants of module add: *)
(* If m>n, Latency of dotproduct with add of latency m =
           (Latency of dotproduct with add of latency n) + (m-n)*k *)
lemma latencyDotproduct_add :
  "(k>0 \<and> ((length v1) = (power 2 k)) \<and> ((length v2) = (power 2 k)) \<and> m>n)
   \<Longrightarrow>
    Latency (Tuple_ofT
              (computeDotProduct mult (Tuple_of2 add2 m r2))
              (global_latencyDotProduct mult (Tuple_of2 add2 m r2) v1 v2 k)
              (reliabilityDotProduct mult (Tuple_of2 add2 m r2) rr k))
    = (Latency (Tuple_ofT
                 (computeDotProduct mult (Tuple_of2 add1 n r1))
                 (global_latencyDotProduct mult (Tuple_of2 add1 n r1) v1 v2 k)
                 (reliabilityDotProduct mult (Tuple_of2 add1 n r1) rr k)))
      + (m-n)*k"
  apply (auto)
  by (metis add_mult_distrib2 le_add_diff_inverse less_or_eq_imp_le mult.commute)

(* Core Dot product with registers on the inputs and the output: *)
lemma themax_latency_reg :
  "v \<noteq> [] \<Longrightarrow> the_max (map (latency \<circ> Reg) v) = 1 + (the_max (map latency v))"
  apply (induct v)
  apply (auto)
  by fastforce

lemma themax_append :
  "the_max (v1 @ v2) = max (the_max v1) (the_max v2)"
  apply (induct v1)
  apply(auto)
  done

lemma latencyDotproduct_regs_in_out :
  "(k>0 \<and> ((length v1) = (power 2 k)) \<and> ((length v2) = (power 2 k)))
   \<Longrightarrow>
     Latency (Tuple_ofT
              (computeDotProduct mul add)
              (global_latencyDotProduct mul add v1 v2 k)
              (reliabilityDotProduct mul add rr k))
    = 2 + (Latency (Tuple_ofT
                 (computeCoreDotProduct mul add)
                 (global_latencyCoreDotProduct mul add v1 v2 k)
                 (reliabilityCoreDotProduct mul add k)))"
  apply (auto)
  by (metis length_0_conv max_Suc_Suc plus_1_eq_Suc power_not_zero themax_append themax_latency_reg zero_neq_numeral)

(* Reliability of dot product for inputs of size 2^(k+1): *)
lemma reliabilityDotProduct_lem1 :
   "k > 0 \<Longrightarrow> 
    reliabilityDotProduct mul add relreg (k+1) =
    (reliabilityParal relreg (k+1)) 
    * (1 + (1-relreg)^(2^(k+1))) 
    * (reliabilityParal (Reliability2 mul) k) 
    * (1 + (1-(Reliability2 mul))^(2^k)) 
    * (reliabilityTree (Reliability2 add) (k-1)) 
    * (reliabilityParal (Reliability2 add) k) * relreg"
  using reliabilityParal_lem1
  apply (auto)
  by (smt (verit, ccfv_threshold) One_nat_def Suc_diff_1 distrib_right mult.assoc mult.commute mult.right_neutral numeral_Bit0 numeral_One numeral_times_numeral one_power2 power_add power_mult_numeral reliabilityParal.elims reliabilityTree.simps(2) square_diff_square_factored)

lemma reliabilityDotProduct_lem2 :
   "k > 0 \<Longrightarrow> 
    reliabilityDotProduct mul add relreg (k+1) =
        (reliabilityDotProduct mul add relreg k) *
        (1 + (1-relreg)^(2^(k+1))) *
        (1 + (1-(Reliability2 mul))^(2^k)) *
        (reliabilityParal (Reliability2 add) k)"
  using reliabilityDotProduct_lem1
  by (smt (verit) mult.commute mult.left_commute reliabilityCoreDotProduct.elims reliabilityDotProduct.elims)

(* Reliability of dot product for inputs of size 2^(k+1) = 
      (Reliability of dot product for inputs of size 2^k) *
      (Reliability for the parallel composition of 2^k add) *
      (1 + (1-Rmul)^(2^k)) * (1 + (1-Rreg)^(2^(k+1)))
*)
lemma reliabilityDotProduct_kplus1 :
  "(k>0 \<and> ((length v1_1) = (power 2 k)) \<and> ((length v2_1) = (power 2 k)))
   \<Longrightarrow>
     Reliability (Tuple_ofT
              (computeDotProduct mul add)
              (global_latencyDotProduct mul add v1 v2 k)
              (reliabilityDotProduct mul add relreg (k+1)))
    = (Reliability (Tuple_ofT
              (computeDotProduct mul add)
              (global_latencyDotProduct mul add v1 v2 k)
              (reliabilityDotProduct mul add relreg k)))
      * (1 + (1-relreg)^(2^(k+1))) 
      * (1 + (1-(Reliability2 mul))^(2^k)) * (reliabilityParal (Reliability2 add) k)"
  using reliabilityDotProduct_lem2
  by (metis CoreprodType.sel(3))

(* 6. Some instantiations for specific adders and multip. *)

(* Combinational adder and multiplier *)
fun fadd_simple :: "nat Signal \<times> nat Signal \<Rightarrow> nat Signal" where
   "fadd_simple (x,y) = Wire ((signal_value x) + (signal_value y))"

fun add_simple :: "real \<Rightarrow> (nat, nat) TwoInputsTrait" where
  "add_simple r = (Tuple_of2 fadd_simple 0 r)"

fun fmul_simple :: "nat Signal \<times> nat Signal \<Rightarrow> nat Signal" where
   "fmul_simple (x,y) = Wire ((signal_value x) * (signal_value y))"

fun mul_simple :: "real \<Rightarrow> (nat, nat) TwoInputsTrait" where
  "mul_simple r = (Tuple_of2 fmul_simple 0 r)"

(* Adder and multiplier with register on the output *)
fun fadd_reg :: "nat Signal \<times> nat Signal \<Rightarrow> nat Signal" where
  "fadd_reg (x,y) = Reg (Wire ((signal_value x) + (signal_value y)))"

fun add_reg :: "real \<Rightarrow> (nat, nat) TwoInputsTrait" where
  "add_reg r = (Tuple_of2 fadd_reg 1 r)"

fun fmul_reg :: "nat Signal \<times> nat Signal \<Rightarrow> nat Signal" where
   "fmul_reg (x,y) = Reg (Wire ((signal_value x) * (signal_value y)))"

fun mul_reg :: "real \<Rightarrow> (nat, nat) TwoInputsTrait" where
  "mul_reg r = (Tuple_of2 fmul_reg 1 r)"

lemma latencyDotproduct_mult_inst1 :
  "(k>0 \<and> ((length v1) = (power 2 k)) \<and> ((length v2) = (power 2 k)) \<and> m>n)
   \<Longrightarrow>
    Latency (Tuple_ofT
              (computeDotProduct (mul_reg r2) add)
              (global_latencyDotProduct (mul_reg r2) add v1 v2 k)
              (reliabilityDotProduct (mul_reg r2) add rr k))
    = (Latency (Tuple_ofT
                 (computeDotProduct (mul_simple r1) add)
                 (global_latencyDotProduct (mul_simple r1) add v1 v2 k)
                 (reliabilityDotProduct (mul_simple r1) add rr k)))
      + 1"
  using latencyDotproduct_mult
  by simp

lemma latencyDotproduct_add_inst1 :
  "(k>0 \<and> ((length v1) = (power 2 k)) \<and> ((length v2) = (power 2 k)) \<and> m>n)
   \<Longrightarrow>
    Latency (Tuple_ofT
              (computeDotProduct mult (add_reg r2))
              (global_latencyDotProduct mult (add_reg r2) v1 v2 k)
              (reliabilityDotProduct mult (add_reg r2) rr k))
    = (Latency (Tuple_ofT
                 (computeDotProduct mult (add_simple r1))
                 (global_latencyDotProduct mult (add_simple r1) v1 v2 k)
                 (reliabilityDotProduct mult (add_simple r1) rr k)))
      + k"
  using latencyDotproduct_add
  by simp

lemma reliabilityDotProduct_kplus1_inst1 :
  "(k>0 \<and> ((length v1_1) = (power 2 k)) \<and> ((length v2_1) = (power 2 k)))
   \<Longrightarrow>
     Reliability (Tuple_ofT
              (computeDotProduct (mul_simple r1) (add_simple r2))
              (global_latencyDotProduct (mul_simple r1) (add_simple r2) v1 v2 k)
              (reliabilityDotProduct (mul_simple r1) (add_simple r2) relreg (k+1)))
    = (Reliability (Tuple_ofT
              (computeDotProduct (mul_simple r1) (add_simple r2))
              (global_latencyDotProduct (mul_simple r1) (add_simple r2) v1 v2 k)
              (reliabilityDotProduct (mul_simple r1) (add_simple r2) relreg k)))
      * (1 + (1-relreg)^(2^(k+1))) 
      * (1 + (1-(Reliability2 (mul_simple r1)))^(2^k)) 
      * (reliabilityParal (Reliability2 (add_simple r2)) k)"
  using reliabilityDotProduct_kplus1
  by blast

lemma reliabilityDotProduct_kplus1_inst2 :
  "(k>0 \<and> ((length v1_1) = (power 2 k)) \<and> ((length v2_1) = (power 2 k)))
   \<Longrightarrow>
     Reliability (Tuple_ofT
              (computeDotProduct (mul_reg r1) (add_reg r2))
              (global_latencyDotProduct (mul_reg r1) (add_reg r2) v1 v2 k)
              (reliabilityDotProduct (mul_reg r1) (add_reg r2) relreg (k+1)))
    = (Reliability (Tuple_ofT
              (computeDotProduct (mul_reg r1) (add_reg r2))
              (global_latencyDotProduct (mul_reg r1) (add_reg r2) v1 v2 k)
              (reliabilityDotProduct (mul_reg r1) (add_reg r2) relreg k)))
      * (1 + (1-relreg)^(2^(k+1))) 
      * (1 + (1-(Reliability2 (mul_reg r1)))^(2^k)) 
      * (reliabilityParal (Reliability2 (add_reg r2)) k)"
  using reliabilityDotProduct_kplus1
  by blast

end
