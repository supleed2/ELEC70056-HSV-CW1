theory HSV_tasks_2022 imports Complex_Main begin

section "Task 1: Full adders"

fun halfadder :: "bool * bool \<Rightarrow> bool * bool"
  where "halfadder (a,b) = (
    let cout = (a \<and> b) in
    let s = (a \<or> b) \<and> \<not>(a \<and> b) in
    (cout, s))"

fun fulladder :: "bool * bool * bool \<Rightarrow> bool * bool"
  where "fulladder (a,b,cin) = (
    let (tmp1, tmp2) = halfadder(a,b) in
    let (tmp3, s) = halfadder(cin,tmp2) in
    let cout = tmp1 | tmp3 in
    (cout, s))"

fun b2i :: "bool \<Rightarrow> int"
  where "b2i (b) = (if (b) then 1 else 0)"

theorem "\<forall>a b.(co,s) = halfadder(a,b) \<Longrightarrow> (2*b2i(co)+b2i(s)) = (b2i(a)+b2i(b))"
  by auto

theorem "\<forall>a b ci.(co,s) = fulladder(a,b,ci) \<Longrightarrow> (2*b2i(co)+b2i(s)) = (b2i(a)+b2i(b)+b2i(ci))"
  by auto

section "Task 2: Fifth powers"

theorem "(n::nat)^5 mod 10 = n mod 10"
proof (induct n)
  case 0
  thus ?case by simp
next
  case (Suc n)
  have d2:"((n::nat)^4 + n) mod 2 = 0" by simp
  hence d10:"(5*((n::nat)^4 + n)) mod 10 = 0"
    by (metis mult_0_right mult_2_right mult_mod_right numeral_Bit0)
  assume IH:"n ^ 5 mod 10 = n mod 10"
  have "(Suc n)^5 = (n + 1)^5" by simp
  have "... = n^5 + 5*(n^4 + n) + 10*n^3 + 10*n^2 + 1" by algebra
  have "... mod 10 = (n^5 + 5*(n^4 + n) + 1) mod 10"
    by (smt (verit, ccfv_SIG) mod_add_cong mod_mult_self2)
  have "... = (n^5 + 1) mod 10" using d10 by auto
  thus ?case by (metis Suc Suc_eq_plus1 \<open>(n + 1) ^ 5 = n ^ 5 + 5 * (n ^ 4 + n) + 10 * n ^ 3 + 10 *
    n\<^sup>2 + 1\<close> \<open>(n ^ 5 + 5 * (n ^ 4 + n) + 10 * n ^ 3 + 10 * n\<^sup>2 + 1) mod 10 = (n ^ 5 + 5 * (n ^ 4 + n)
    + 1) mod 10\<close> mod_Suc_eq)
qed

theorem "\<exists>n::nat.(n^6 mod 10 \<noteq> n mod 10)" by (rule exI[where x = 2], simp)

section "Task 3: Logic optimisation"

(* Datatype for representing simple circuits. *)
datatype "circuit" =
  NOT "circuit"
| AND "circuit" "circuit"
| OR "circuit" "circuit"
| TRUE
| FALSE
| INPUT "int"

(* Simulates a circuit given a valuation for each input wire. *)
fun simulate :: "circuit \<Rightarrow> (int \<Rightarrow> bool) \<Rightarrow> bool" where
  "simulate (AND c1 c2) \<rho> = ((simulate c1 \<rho>) \<and> (simulate c2 \<rho>))"
| "simulate (OR c1 c2) \<rho> = ((simulate c1 \<rho>) \<or> (simulate c2 \<rho>))"
| "simulate (NOT c) \<rho> = (\<not> (simulate c \<rho>))"
| "simulate TRUE \<rho> = True"
| "simulate FALSE \<rho> = False"
| "simulate (INPUT i) \<rho> = \<rho> i"

(* Equivalence between circuits. *)
fun circuits_equiv (infix "\<sim>" 50) (* the "50" indicates the operator precedence *) where
  "c1 \<sim> c2 = (\<forall>\<rho>. simulate c1 \<rho> = simulate c2 \<rho>)"

(* An optimisation that exploits the following Boolean identities:
  `a | a = a`
  `a & a = a`
 *)
fun opt_ident :: "circuit \<Rightarrow> circuit" where
  "opt_ident (NOT c) = NOT (opt_ident c)"
| "opt_ident (AND c1 c2) = (
   let c1' = opt_ident c1 in
   let c2' = opt_ident c2 in
   if c1' = c2' then c1' else AND c1' c2')"
| "opt_ident (OR c1 c2) = (
   let c1' = opt_ident c1 in
   let c2' = opt_ident c2 in
   if c1' = c2' then c1' else OR c1' c2')"
| "opt_ident TRUE = TRUE"
| "opt_ident FALSE = FALSE"
| "opt_ident (INPUT i) = INPUT i"

lemma "opt_ident (AND (INPUT 1) (OR (INPUT 1) (INPUT 1))) = INPUT 1" by eval (* test case *)

theorem opt_ident_is_sound: "opt_ident c \<sim> c"
proof (induct c)
  case (AND c1 c2)
  thus ?case by (smt circuits_equiv.simps opt_ident.simps(2) simulate.simps(1))
next
  case (OR c1 c2)
  thus ?case by (smt circuits_equiv.simps opt_ident.simps(3) simulate.simps(2))
qed(simp+)

fun area :: "circuit \<Rightarrow> nat" where
  "area (NOT c) = 1 + area c"
| "area (AND c1 c2) = 1 + area c1 + area c2"
| "area (OR c1 c2) = 1 + area c1 + area c2"
| "area _ = 0"

theorem opt_ident_never_inc_area: "area (opt_ident c) \<le> area c"
proof (induct c)
  case (AND c1 c2)
  {
    assume "opt_ident c1 = opt_ident c2"
    hence "area (opt_ident (AND c1 c2)) = area (opt_ident c1)" by simp
    hence "area (opt_ident (AND c1 c2)) \<le> area (AND (opt_ident c1) (opt_ident c2))" by simp
    hence ?case using AND.hyps(2) \<open>opt_ident c1 = opt_ident c2\<close> by auto
  }
  moreover
  {
    assume "opt_ident c1 \<noteq> opt_ident c2"
    hence "area (opt_ident (AND c1 c2)) = area (AND (opt_ident c1) (opt_ident c2))" by simp
    hence ?case by (simp add: AND.hyps(1) AND.hyps(2) add_mono_thms_linordered_semiring(1))
  }
  ultimately show ?case by fastforce
next
  case (OR c1 c2)
  {
    assume "opt_ident c1 = opt_ident c2"
    hence "area (opt_ident (OR c1 c2)) = area (opt_ident c1)" by simp
    hence "area (opt_ident (OR c1 c2)) \<le> area (OR (opt_ident c1) (opt_ident c2))" by simp
    hence ?case using OR.hyps(2) \<open>opt_ident c1 = opt_ident c2\<close> by auto
  }
  moreover
  {
    assume "opt_ident c1 \<noteq> opt_ident c2"
    hence "area (opt_ident (OR c1 c2)) = area (OR (opt_ident c1) (opt_ident c2))" by simp
    hence ?case by (simp add: OR.hyps(1) OR.hyps(2) add_mono_thms_linordered_semiring(1))
  }
  ultimately show ?case by fastforce
qed(simp+)

section "Task 4: More logic optimisation"

(* An optimisation that exploits the following Boolean identities:
  `a | (a & b) = a`
  `(a & b) | a = a`
  `a & (a | b) = a`
  `(a | b) & a = a`
 *)
fun opt_redundancy :: "circuit \<Rightarrow> circuit" where
  "opt_redundancy (NOT c) = NOT (opt_redundancy c)"
| "opt_redundancy (OR c1 (AND c2 c3)) = (
   let c1' = opt_redundancy c1 in
   let c2' = opt_redundancy c2 in
   let c3' = opt_redundancy c3 in
   if c1' = c2' | c1' = c3' then c1'
   else OR c1' (AND c2' c3'))"
| "opt_redundancy (OR (AND c1 c2) c3) = (
   let c1' = opt_redundancy c1 in
   let c2' = opt_redundancy c2 in
   let c3' = opt_redundancy c3 in
   if c1' = c3' | c2' = c3' then c3'
   else (OR (AND c1' c2') c3'))"
| "opt_redundancy (AND c1 (OR c2 c3)) = (
   let c1' = opt_redundancy c1 in
   let c2' = opt_redundancy c2 in
   let c3' = opt_redundancy c3 in
   if c1' = c2' | c1' = c3' then c1'
   else AND c1' (OR c2' c3'))"
| "opt_redundancy (AND (OR c1 c2) c3) = (
   let c1' = opt_redundancy c1 in
   let c2' = opt_redundancy c2 in
   let c3' = opt_redundancy c3 in
   if c1' = c3' | c2' = c3' then c3'
   else (AND (OR c1' c2') c3'))"
| "opt_redundancy (AND c1 c2) = (
   let c1' = opt_redundancy c1 in
   let c2' = opt_redundancy c2 in
   if c1' = c2' then c1' else AND c1' c2')"
| "opt_redundancy (OR c1 c2) = (
   let c1' = opt_redundancy c1 in
   let c2' = opt_redundancy c2 in
   if c1' = c2' then c1' else OR c1' c2')"
| "opt_redundancy TRUE = TRUE"
| "opt_redundancy FALSE = FALSE"
| "opt_redundancy (INPUT i) = INPUT i"

lemma "opt_redundancy (AND (INPUT 1)
                           (OR (INPUT 1)
                               (INPUT 2))) = INPUT 1" by eval (* test case *)

lemma "opt_redundancy (AND (AND (INPUT 1)
                                (OR (INPUT 1)
                                    (INPUT 2)))
                           (OR (AND (INPUT 1)
                                    (OR (INPUT 1)
                                        (INPUT 2)))
                               (INPUT 2))) = INPUT 1" by eval (* test case *)

lemma "opt_redundancy (AND (AND (INPUT 1)
                                (OR (INPUT 1)
                                    (INPUT 2)))
                           (OR (INPUT 2)
                               (AND (INPUT 1)
                                    (OR (INPUT 1)
                                        (INPUT 2))))) = INPUT 1" by eval (* test case *)

lemma "opt_redundancy (AND (AND (AND (INPUT 1)
                                     (OR (INPUT 1)
                                         (INPUT 2)))
                                (OR (INPUT 2)
                                    (AND (INPUT 1)
                                         (OR (INPUT 1)
                                             (INPUT 2)))))
                           (OR (INPUT 1)
                               (INPUT 2))) = INPUT 1" by eval (* test case *)

theorem opt_redundancy_is_sound: "opt_redundancy c \<sim> c"
proof (induct rule:opt_redundancy.induct)
  case (2 c1 c2 c3)
  thus ?case by (smt (verit) opt_redundancy.simps(2) circuits_equiv.elims(1) simulate.simps(1) simulate.simps(2))
next
  case ("3_1" c1 c2 v)
  thus ?case by (smt (verit) opt_redundancy.simps(3) circuits_equiv.elims(1) simulate.simps(1) simulate.simps(2))
next
  case ("3_2" c1 c2 v va)
  thus ?case by (smt (verit) opt_redundancy.simps(4) circuits_equiv.elims(1) simulate.simps(1) simulate.simps(2))
next
  case ("3_3" c1 c2)
  thus ?case by (smt (verit) opt_redundancy.simps(5) circuits_equiv.elims(1) simulate.simps(1) simulate.simps(2))
next
  case ("3_4" c1 c2)
  thus ?case by (smt (verit) opt_redundancy.simps(6) circuits_equiv.elims(1) simulate.simps(1) simulate.simps(2))
next
  case ("3_5" c1 c2 v)
  thus ?case by (smt (verit) opt_redundancy.simps(7) circuits_equiv.elims(1) simulate.simps(1) simulate.simps(2))
next
  case (4 c1 c2 c3)
  thus ?case by (smt (verit) opt_redundancy.simps(8) circuits_equiv.elims(1) simulate.simps(1) simulate.simps(2))
next
  case ("5_1" c1 c2 v)
  thus ?case by (smt (verit) opt_redundancy.simps(9) circuits_equiv.elims(1) simulate.simps(1) simulate.simps(2))
next
  case ("5_2" c1 c2 v va)
  thus ?case by (smt (verit) opt_redundancy.simps(10) circuits_equiv.elims(1) simulate.simps(1) simulate.simps(2))
next
  case ("5_3" c1 c2)
  thus ?case by (smt (verit) opt_redundancy.simps(11) circuits_equiv.elims(1) simulate.simps(1) simulate.simps(2))
next
  case ("5_4" c1 c2)
  thus ?case by (smt (verit) opt_redundancy.simps(12) circuits_equiv.elims(1) simulate.simps(1) simulate.simps(2))
next
  case ("5_5" c1 c2 v)
  thus ?case by (smt (verit) opt_redundancy.simps(13) circuits_equiv.elims(1) simulate.simps(1) simulate.simps(2))
next
  case ("6_1" va v)
  thus ?case by (smt (verit) opt_redundancy.simps(14) circuits_equiv.elims(1) simulate.simps(1) simulate.simps(2))
next
  case ("6_2" va vb v)
  thus ?case by (smt (verit) opt_redundancy.simps(15) circuits_equiv.elims(1) simulate.simps(1) simulate.simps(2))
next
  case ("6_6" vb v va)
  thus ?case by (smt (verit) opt_redundancy.simps(19) circuits_equiv.elims(1) simulate.simps(1) simulate.simps(2))
next
  case ("6_7" vb vc v va)
  thus ?case by (smt (verit) opt_redundancy.simps(20) circuits_equiv.elims(1) simulate.simps(1) simulate.simps(2))
next
  case ("6_8" v va)
  thus ?case by (smt (verit) opt_redundancy.simps(21) circuits_equiv.elims(1) simulate.simps(1) simulate.simps(2))
next
  case ("6_9" v va)
  thus ?case by (smt (verit) opt_redundancy.simps(22) circuits_equiv.elims(1) simulate.simps(1) simulate.simps(2))
next
  case ("6_10" vb v va)
  thus ?case by (smt (verit) opt_redundancy.simps(23) circuits_equiv.elims(1) simulate.simps(1) simulate.simps(2))
next
  case ("6_12" v va)
  thus ?case by (smt (verit) opt_redundancy.simps(25) circuits_equiv.elims(1) simulate.simps(1) simulate.simps(2))
next
  case ("6_17" v va)
  thus ?case by (smt (verit) opt_redundancy.simps(30) circuits_equiv.elims(1) simulate.simps(1) simulate.simps(2))
next
  case ("6_22" va vb v)
  thus ?case by (smt (verit) opt_redundancy.simps(35) circuits_equiv.elims(1) simulate.simps(1) simulate.simps(2))
next
  case ("6_25" va v)
  thus ?case by (smt (verit) opt_redundancy.simps(38) circuits_equiv.elims(1) simulate.simps(1) simulate.simps(2))
next
  case ("7_1" va v)
  thus ?case by (smt (verit) opt_redundancy.simps(39) circuits_equiv.elims(1) simulate.simps(1) simulate.simps(2))
next
  case ("7_2" va vb v)
  thus ?case by (smt (verit) opt_redundancy.simps(40) circuits_equiv.elims(1) simulate.simps(1) simulate.simps(2))
next
  case ("7_6" vb v va)
  thus ?case by (smt (verit) opt_redundancy.simps(44) circuits_equiv.elims(1) simulate.simps(1) simulate.simps(2))
next
  case ("7_7" vb vc v va)
  thus ?case by (smt (verit) opt_redundancy.simps(45) circuits_equiv.elims(1) simulate.simps(1) simulate.simps(2))
next
  case ("7_8" v va)
  thus ?case by (smt (verit) opt_redundancy.simps(46) circuits_equiv.elims(1) simulate.simps(1) simulate.simps(2))
next
  case ("7_9" v va)
  thus ?case by (smt (verit) opt_redundancy.simps(47) circuits_equiv.elims(1) simulate.simps(1) simulate.simps(2))
next
  case ("7_10" vb v va)
  thus ?case by (smt (verit) opt_redundancy.simps(48) circuits_equiv.elims(1) simulate.simps(1) simulate.simps(2))
next
  case ("7_12" v va)
  thus ?case by (smt (verit) opt_redundancy.simps(50) circuits_equiv.elims(1) simulate.simps(1) simulate.simps(2))
next
  case ("7_17" v va)
  thus ?case by (smt (verit) opt_redundancy.simps(55) circuits_equiv.elims(1) simulate.simps(1) simulate.simps(2))
next
  case ("7_22" va vb v)
  thus ?case by (smt (verit) opt_redundancy.simps(60) circuits_equiv.elims(1) simulate.simps(1) simulate.simps(2))
next
  case ("7_25" va v)
  thus ?case by (smt (verit) opt_redundancy.simps(63) circuits_equiv.elims(1) simulate.simps(1) simulate.simps(2))
qed(simp+)

theorem opt_redundancy_never_inc_area: "area (opt_redundancy c) \<le> area c"
proof (induct rule:opt_redundancy.induct) case (2 c1 c2 c3)
  thus ?case by (smt (verit, ccfv_threshold) add_leE add_mono_thms_linordered_semiring(1) area.simps(2) area.simps(3) circuit.inject(3) not_less_eq_eq opt_redundancy.simps(2) plus_1_eq_Suc)
next case ("3_1" c1 c2 c3)
  thus ?case by (smt (verit, del_insts) add_leE add_mono_thms_linordered_semiring(1) area.simps(3) area.simps(2) nle_le opt_redundancy.simps(3))
next case ("3_2" c1 c2 c3 c4)
  thus ?case by (smt (verit, ccfv_threshold) Suc_leI add_mono_thms_linordered_semiring(1) area.simps(3) area.simps(2) less_Suc_eq_le opt_redundancy.simps(4) plus_1_eq_Suc trans_le_add2)
next case ("3_3" c1 c2)
  thus ?case by (smt (verit) add_mono_thms_linordered_semiring(1) area.simps(2) area.simps(3) area.simps(4) dual_order.eq_iff less_Suc_eq_0_disj less_Suc_eq_le opt_redundancy.simps(5))
next case ("3_4" c1 c2)
  thus ?case by (smt (verit) add_mono_thms_linordered_semiring(1) area.simps(2) area.simps(3) area.simps(5) dual_order.eq_iff less_Suc_eq_0_disj less_Suc_eq_le opt_redundancy.simps(6))
next case ("3_5" c1 c2 c3)
  let ?c1' = "opt_redundancy c1"
  let ?c2' = "opt_redundancy c2"
  from "3_5" have IH:"area (OR (AND ?c1' ?c2') (INPUT c3)) \<le> area (OR (AND c1 c2) (INPUT c3))" by auto
  hence "area (opt_redundancy (OR (AND c1 c2) (INPUT c3))) \<le> area (OR (AND ?c1' ?c2') (INPUT c3))"
    by (smt area.simps(6) bot_nat_0.extremum_unique nat_le_linear opt_redundancy.simps(66) opt_redundancy.simps(7))
  thus ?case using IH by linarith
next case (4 c1 c2 c3)
  thus ?case by (smt (verit, ccfv_threshold) add_leE add_mono_thms_linordered_semiring(1) area.simps(2) area.simps(3) not_less_eq_eq opt_redundancy.simps(8) plus_1_eq_Suc)
next case ("5_1" c1 c2 c3)
  thus ?case by (smt (verit, del_insts) add_leE add_mono_thms_linordered_semiring(1) area.simps(2) area.simps(3) nle_le opt_redundancy.simps(9))
next case ("5_2" c1 c2 c3 c4)
  thus ?case by (smt (verit, del_insts) Suc_leI add_mono_thms_linordered_semiring(1) area.simps(2) area.simps(3) less_Suc_eq_le opt_redundancy.simps(10) plus_1_eq_Suc trans_le_add2)
next case ("5_3" c1 c2)
  thus ?case by (smt (verit, ccfv_threshold) add_mono_thms_linordered_semiring(1) area.simps(2) area.simps(3) area.simps(4) bot_nat_0.extremum_unique nat_le_linear opt_redundancy.simps(11))
next case ("5_4" c1 c2)
  thus ?case by (smt (verit, ccfv_threshold) add_mono_thms_linordered_semiring(1) area.simps(2) area.simps(3) area.simps(5) bot_nat_0.extremum_unique nat_le_linear opt_redundancy.simps(12))
next case ("5_5" c1 c2 c3)
  thus ?case by (smt (verit, del_insts) add_leE add_mono_thms_linordered_semiring(1) area.simps(2) area.simps(3) not_less_eq_eq opt_redundancy.simps(13) plus_1_eq_Suc)
next case ("6_1" c1 c2)
  thus ?case by (smt (verit) add_leE add_mono_thms_linordered_semiring(1) area.simps(2) not_less_eq_eq opt_redundancy.simps(14) plus_1_eq_Suc)
next case ("6_2" c1 c2 c3)
  thus ?case by (smt (verit) add_leE add_mono_thms_linordered_semiring(1) area.simps(2) nat_le_linear opt_redundancy.simps(15))
next case ("6_6" c1 c2 c3)
  thus ?case by (smt (verit) add_leE add_mono_thms_linordered_semiring(1) area.simps(2) not_less_eq_eq opt_redundancy.simps(19) plus_1_eq_Suc)
next case ("6_7" c1 c2 c3 c4)
  thus ?case by (smt add_leD1 add_le_mono area.simps(2) le_cases3 not_less_eq_eq opt_redundancy.simps(20) plus_1_eq_Suc)
next case ("6_8" c1 c2)
  thus ?case by (smt One_nat_def area.simps(2) area.simps(4) nat_le_linear not_less_eq_eq opt_redundancy.simps(21) opt_redundancy.simps(64) plus_1_eq_Suc)
next case ("6_9" c1 c2)
  thus ?case by (smt One_nat_def area.simps(2) area.simps(5) nat_le_linear not_less_eq_eq opt_redundancy.simps(22) opt_redundancy.simps(65) plus_1_eq_Suc)
next case ("6_10" c1 c2 c3)
  thus ?case by (smt One_nat_def area.simps(2) area.simps(6) nat_le_linear not_less_eq_eq opt_redundancy.simps(23) opt_redundancy.simps(66) plus_1_eq_Suc)
next case ("6_12" c1 c2)
  thus ?case by (smt add_cancel_right_right area.simps(2) area.simps(4) linorder_linear not_less_eq_eq opt_redundancy.simps(25) opt_redundancy.simps(64) plus_1_eq_Suc)
next case ("6_17" c1 c2)
  thus ?case by (smt (verit) add_leE add_mono_thms_linordered_semiring(1) area.simps(2) not_less_eq_eq opt_redundancy.simps(30) plus_1_eq_Suc)
next case ("6_22" c1 c2 c3)
  thus ?case by (smt add_cancel_right_right add_mono_thms_linordered_semiring(1) area.simps(2) area.simps(6) nat_le_linear not_less_eq_eq opt_redundancy.simps(35) plus_1_eq_Suc)
next case ("6_25" c1 c2)
  thus ?case by (metis (full_types) area.simps(6) bot_nat_0.extremum opt_redundancy.simps(38) opt_redundancy.simps(66) verit_comp_simplify1(2))
next case ("7_1" c1 c2)
  thus ?case by (smt (verit) Suc_leI add_mono_thms_linordered_semiring(1) area.simps(3) le_imp_less_Suc opt_redundancy.simps(39) plus_1_eq_Suc trans_le_add2)
next case ("7_2" c1 c2 c3)
  thus ?case by (smt (verit) add_leD1 add_mono_thms_linordered_semiring(1) area.simps(3) nat_le_linear not_less_eq_eq opt_redundancy.simps(40) plus_1_eq_Suc)
next case ("7_6" c1 c2 c3)
  thus ?case by (smt (verit) add_leE add_mono_thms_linordered_semiring(1) area.simps(3) nat_le_linear opt_redundancy.simps(44))
next case ("7_7" c1 c2 c3 c4)
  thus ?case by (smt (verit) add_leD1 add_le_mono area.simps(3) le_cases3 not_less_eq_eq opt_redundancy.simps(45) plus_1_eq_Suc)
next case ("7_8" c1 c2)
  thus ?case by (smt One_nat_def Suc_le_mono area.simps(3) area.simps(4) le_SucI opt_redundancy.simps(46) opt_redundancy.simps(64) plus_1_eq_Suc)
next case ("7_9" c1 c2)
  thus ?case by (smt One_nat_def Suc_le_mono area.simps(3) area.simps(5) le_Suc_eq opt_redundancy.simps(47) opt_redundancy.simps(65) plus_1_eq_Suc)
next case ("7_10" c1 c2 c3)
  thus ?case by (smt add.right_neutral area.simps(3) area.simps(6) nat_le_linear not_less_eq_eq opt_redundancy.simps(48) opt_redundancy.simps(66) plus_1_eq_Suc)
next case ("7_12" c1 c2)
  thus ?case by (smt add_leE add_mono_thms_linordered_semiring(1) area.simps(3) not_less_eq_eq opt_redundancy.simps(50) plus_1_eq_Suc)
next case ("7_17" c1 c2)
  thus ?case by (smt (verit) add_leE add_mono_thms_linordered_semiring(1) area.simps(3) not_less_eq_eq opt_redundancy.simps(55) plus_1_eq_Suc)
next case ("7_22" c1 c2 c3)
  thus ?case by (smt add.right_neutral area.simps(3) area.simps(6) bot_nat_0.extremum_unique nle_le not_less_eq_eq opt_redundancy.simps(60) plus_1_eq_Suc)
next case ("7_25" c1 c2)
  thus ?case by (metis (full_types) area.simps(6) opt_redundancy.simps(63) opt_redundancy.simps(66) order_refl zero_le)
qed(simp+)

end