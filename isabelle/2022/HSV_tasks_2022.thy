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

section {* Task 3: Logic optimisation *}

(* Datatype for representing simple circuits. *)
datatype "circuit" = 
  NOT "circuit"
| AND "circuit" "circuit"
| OR "circuit" "circuit"
| TRUE
| FALSE
| INPUT "int"

(* Simulates a circuit given a valuation for each input wire. *)
fun simulate where
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
fun opt_ident where
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

lemma (* test case *) 
  "opt_ident (AND (INPUT 1) (OR (INPUT 1) (INPUT 1))) = INPUT 1" 
by eval

theorem opt_ident_is_sound: "opt_ident c \<sim> c"
  oops

fun area :: "circuit \<Rightarrow> nat" where
  "area (NOT c) = 1 + area c"
| "area (AND c1 c2) = 1 + area c1 + area c2"
| "area (OR c1 c2) = 1 + area c1 + area c2"
| "area _ = 0"

section {* Task 4: More logic optimisation *}

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