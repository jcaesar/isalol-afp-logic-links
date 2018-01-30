theory BEXPC_PPS
imports Boolean_Expression_Checkers.Boolean_Expression_Checkers "Propositional_Proof_Systems.Sema"
begin

text \<open>Easy: @{typ "'a ifex \<Rightarrow> 'a formula"}.\<close>

primrec form_of_ifex where
"form_of_ifex Trueif = \<^bold>\<not> \<bottom>" |
"form_of_ifex Falseif = \<bottom>" |
"form_of_ifex (IF n t1 t2) =
  (Atom n \<^bold>\<and> form_of_ifex t1) \<^bold>\<or> (\<^bold>\<not> (Atom n) \<^bold>\<and> form_of_ifex t2)"

lemma form_of_ifex: "\<A> \<Turnstile> form_of_ifex T \<longleftrightarrow> val_ifex T \<A>"
  by(induction T; simp)

text \<open>A little bit tricky: @{typ "'a formula \<Rightarrow> 'a ifex"}.\<close>

(* abusing normif as a kind of IfThenElse-operator *)
text\<open>Does what @{const ifex_of} does.\<close>
find_consts "'b ifex \<Rightarrow> 'b ifex \<Rightarrow> 'b ifex \<Rightarrow> 'b ifex"
find_theorems normif
primrec ifex_of_form where
"ifex_of_form \<bottom> = Falseif" |
"ifex_of_form (Atom n) = IF n Trueif Falseif" |
"ifex_of_form (\<^bold>\<not>F) = normif Mapping.empty (ifex_of_form F) Falseif Trueif" |
"ifex_of_form (F \<^bold>\<and> G) = normif Mapping.empty (ifex_of_form F) (ifex_of_form G) Falseif" |
"ifex_of_form (F \<^bold>\<or> G) = normif Mapping.empty (ifex_of_form F) Trueif (ifex_of_form G)" |
"ifex_of_form (F \<^bold>\<rightarrow> G) = normif Mapping.empty (ifex_of_form F) (ifex_of_form G) Trueif"

lemma ifex_of_form: "val_ifex (ifex_of_form T) \<A> \<longleftrightarrow> \<A> \<Turnstile> T"
  by(induction T; simp add: agree_Nil val_normif)

text\<open>The rest is obvious.\<close>

primrec bool_expr_of_form where
"bool_expr_of_form \<bottom> = Const_bool_expr False" |
"bool_expr_of_form (Atom n) = Atom_bool_expr n" |
"bool_expr_of_form (\<^bold>\<not>F) = Neg_bool_expr (bool_expr_of_form F)" |
"bool_expr_of_form (F \<^bold>\<and> G) = And_bool_expr (bool_expr_of_form F) (bool_expr_of_form G)" |
"bool_expr_of_form (F \<^bold>\<or> G) = Or_bool_expr (bool_expr_of_form F) (bool_expr_of_form G)" |
"bool_expr_of_form (F \<^bold>\<rightarrow> G) = Imp_bool_expr (bool_expr_of_form F) (bool_expr_of_form G)"

lemma bool_expr_of_form: "val_bool_expr (bool_expr_of_form F) \<A> \<longleftrightarrow> \<A> \<Turnstile> F"
  by(induction F; simp)

primrec form_of_bool_expr where
"form_of_bool_expr (Const_bool_expr c) = (if c then \<top> else \<bottom>)" |
"form_of_bool_expr (Atom_bool_expr n) = Atom n" |
"form_of_bool_expr (Neg_bool_expr b) = \<^bold>\<not>(form_of_bool_expr b)" |
"form_of_bool_expr (And_bool_expr b1 b2) = (form_of_bool_expr b1) \<^bold>\<and> (form_of_bool_expr b2)" |
"form_of_bool_expr (Or_bool_expr b1 b2) = (form_of_bool_expr b1) \<^bold>\<or> (form_of_bool_expr b2)" |
"form_of_bool_expr (Imp_bool_expr b1 b2) = (form_of_bool_expr b1) \<^bold>\<rightarrow> (form_of_bool_expr b2)" |
"form_of_bool_expr (Iff_bool_expr b1 b2) = 
  (let F = (form_of_bool_expr b1); G = (form_of_bool_expr b2) in
  (F \<^bold>\<rightarrow> G) \<^bold>\<and> (G \<^bold>\<rightarrow> F))" (* potentially exponential\<dots> *)

lemma form_of_bool_expr: "val_bool_expr b \<A> \<longleftrightarrow> \<A> \<Turnstile> (form_of_bool_expr b)"
  by(induction b; auto simp add: Let_def)

end