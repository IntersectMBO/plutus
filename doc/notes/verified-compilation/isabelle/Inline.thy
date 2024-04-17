section \<open>Outline\<close>
text \<open>This is just an experiment with presenting the datatypes and relations from Jacco's
      paper in Iasbelle and working out how well (or otherwise) sledgehamemr et al. can handle
      generating proofs for them. \<close>

theory Inline
  imports 
    Main
    HOL.String
    HOL.List
begin

type_synonym Name = string

section \<open>Simple Lambda Calculus\<close>

text \<open>A very cut down lambda calculus with just enough to demo the functions below. \<close>

text \<open>I have commented out the Let definition because it produces some slightly complicated
      variable name shadowing issues that wouldn't really help with this demo. \<close>

datatype AST = Var Name
  | Lam Name AST
  | App AST AST
(*   | Let Name AST AST *) (* The definition below does some name introduction without 
                              checking things are free, which could cause shadowing, 
                              which in turn makes the proofs harder...*)

text \<open>Simple variable substitution is useful later.\<close>

fun subst :: "AST \<Rightarrow> Name \<Rightarrow> AST \<Rightarrow> AST" where
"subst (Var n) m e = (if (n = m) then e else Var n)"
| "subst (Lam x e) m e' = Lam x (subst e m e')"
| "subst (App a b) m e' = App (subst a m e') (subst b m e')"
(* | "subst (Let x xv e) m e' = (Let x (subst xv m e') (subst e m e'))" (* how should this work if x = m? *) *)

text \<open>Beta reduction is just substitution when done right. 
      This isn't actually used in this demo, but it works...\<close>

fun beta_reduce :: "AST \<Rightarrow> AST" where
"beta_reduce (App (Lam n e) x) = (subst e n x)"
| "beta_reduce e = e"

section \<open>Translation Relation\<close>

text \<open>In a context, it is valid to inline variable values.\<close>

type_synonym Context = "Name \<Rightarrow> AST"

fun extend :: "Context \<Rightarrow> (Name * AST) \<Rightarrow> Context" where
"extend \<Gamma> (n, ast) = (\<lambda> x . if (x = n) then ast else \<Gamma> x)"

text \<open>This defintion is from figure 2 of 
      [the paper](https://iohk.io/en/research/library/papers/translation-certification-for-smart-contracts-scp/)\<close>

inductive inline :: "Context \<Rightarrow> AST \<Rightarrow> AST \<Rightarrow> bool" ("_ \<turnstile> _ \<triangleright> _" 60) where
"\<lbrakk>(\<Gamma> x) = y ; \<Gamma> \<turnstile> y \<triangleright> y' \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> (Var x) \<triangleright> y'"
| "\<Gamma> \<turnstile> (Var x) \<triangleright> (Var x)"
(* | "\<lbrakk> \<Gamma> \<turnstile> t1 \<triangleright> t1' ; (extend \<Gamma> (x,t1)) \<turnstile> t2 \<triangleright> t2' \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> (Let x t1 t2) \<triangleright> (Let x t1' t2')" *)
| "\<lbrakk> \<Gamma> \<turnstile> t1 \<triangleright> t1' ; \<Gamma> \<turnstile> t2 \<triangleright> t2' \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> App t1 t2 \<triangleright> App t1' t2'"
| "\<Gamma> \<turnstile> t1 \<triangleright> t1' \<Longrightarrow> \<Gamma> \<turnstile> Lam x t1 \<triangleright> Lam x t1'"

text \<open>Idempotency is useful for resolving inductive substitutions.\<close>

lemma inline_idempotent : "\<Gamma> \<turnstile> x \<triangleright> x"
proof (induct x)
  case (Var x)
  then show ?case by (rule inline.intros(2))
next
  case (Lam x1a x)
  then show ?case by (rule inline.intros(4))
next
  case (App x1 x2)
  then show ?case by (rule inline.intros(3))
(* This requires x1a to be free in x1 and x2, or to shadow in a consistent way, which is a hassle to demonstrate...
next
  case (Let x1a x1 x2)
  then show ?case
    apply (rule_tac ?x="x1a" in VerifiedCompilation.inline.intros(3))
     apply simp
*) 
qed

section \<open>Experiments\<close>

text \<open>We can present some simple pairs of ASTs and ask sledgehammer to produce proofs.
      For all of these it just works with the simplifier, since they are just applications
      of the definition of the translation. \<close>

lemma demo_inline1 : "\<lbrakk> \<Gamma> x = (Var y) \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> (Var x) \<triangleright> (Var y)"
  by (simp add: inline.intros(1) inline_idempotent)

lemma demo_inline2 : "\<lbrakk> \<Gamma> f = (Lam x (App g (Var x))) ; \<Gamma> y = (Var b) \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> (App (Var f) (Var y)) \<triangleright> (App (Lam x (App g (Var x))) (Var b))"
  by (simp add: inline.intros(1) inline.intros(3) inline_idempotent)

lemma demo_inline_2step : "\<lbrakk> \<Gamma> f = (Lam x (Lam y (App (Var x) (Var y)))) ; \<Gamma> b = (Var z) \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> (App (Var f) (Var b)) \<triangleright> (App (Lam x (Lam y (App (Var x) (Var y)))) (Var z))"
  by (simp add: inline.intros(1) inline.intros(3) inline_idempotent)

lemma demo_inline_4step : "\<lbrakk> \<Gamma> f = (Lam x (Lam y (App (Var x) (Var y)))) ; \<Gamma> b = (Var c) ; \<Gamma> c = (Var d) ; \<Gamma> d = (App (Var i) (Var j)) \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> (App (Var f) (Var b)) \<triangleright> (App (Lam x (Lam y (App (Var x) (Var y)))) (App (Var i) (Var j)))"
  using inline.intros(1) inline.intros(3) inline_idempotent by presburger

text \<open>A false example to show verification actually happen! This reqriting isn't valid and 
       nitpick can show you a counterexample pretty quickly (although it isn't very readable).\<close>
lemma demo_wrong_inline : "\<lbrakk> \<Gamma> f = (Lam x (Lam y (App (Var x) (Var y)))) \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> (App (Var f) (Var z)) \<triangleright> (App (Var x) (Var y))"
  nitpick
  sorry

end

