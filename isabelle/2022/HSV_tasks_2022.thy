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

lemma (* test case *) 
  "opt_redundancy (AND (INPUT 1) (OR (INPUT 1) (INPUT 2))) 
   = INPUT 1" 
  (* by eval *) oops
lemma (* test case *) 
  "opt_redundancy (AND (AND (INPUT 1) (OR (INPUT 1) (INPUT 2)))
                       (OR (AND (INPUT 1) (OR (INPUT 1) (INPUT 2))) (INPUT 2))) 
   = INPUT 1" 
  (* by eval *) oops
lemma (* test case *) 
  "opt_redundancy (AND (AND (INPUT 1) (OR (INPUT 1) (INPUT 2))) 
                       (OR (INPUT 2) (AND (INPUT 1) (OR (INPUT 1) (INPUT 2))))) 
   = INPUT 1"
  (* by eval *) oops
lemma (* test case *) 
  "opt_redundancy (AND (AND (AND (INPUT 1) (OR (INPUT 1) (INPUT 2))) 
                            (OR (INPUT 2) (AND (INPUT 1) (OR (INPUT 1) (INPUT 2))))) 
                       (OR (INPUT 1) (INPUT 2))) 
  = INPUT 1" 
  (* by eval *) oops

end