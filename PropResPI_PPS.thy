theory PropResPI_PPS
  imports PropResPI.Propositional_Resolution Propositional_Proof_Systems.CNF_Sema
(* Uuuh, I smell naming clashes. *)
begin


locale PRPI_PPS = propositional_atoms 
begin

primrec pplit_of_prlit :: "'a Literal \<Rightarrow> 'a literal" where
"pplit_of_prlit (Pos a) = a\<^sup>+" |
"pplit_of_prlit (Neg a) = a\<inverse>"
primrec prlit_of_pplit :: "'a literal \<Rightarrow> 'a Literal" where
"prlit_of_pplit (a\<^sup>+) = (Pos a)" |
"prlit_of_pplit (a\<inverse>) = (Neg a)"
definition "ppcnf_of_prform = (op ` \<circ> op `) pplit_of_prlit"
definition "prform_of_ppcnf = (op ` \<circ> op `) prlit_of_pplit"

definition "ppval_of_printerp (I :: 'a Interpretation) \<equiv> (\<lambda>n. n \<in> I)"
definition "printerp_of_ppval \<A> = Collect \<A>"


lemmas ppprdefs = ppcnf_of_prform_def prform_of_ppcnf_def
                 ppval_of_printerp_def printerp_of_ppval_def

lemma ppprlit: "lit_semantics v (pplit_of_prlit x) = validate_literal (printerp_of_ppval v) x"
  by(cases x; simp add: ppprdefs)
  

lemma pppr_vicf: "cnf_semantics (ppval_of_printerp I) (ppcnf_of_prform S) = validate_formula I S"
proof -
  have "lit_semantics (\<lambda>n. n \<in> I) (pplit_of_prlit x) = I \<Turnstile> x" for x
    by(cases x; simp)
  hence "Bex (pplit_of_prlit ` x) (lit_semantics (\<lambda>n. n \<in> I)) = I \<Turnstile> x" for x 
    unfolding bex_simps validate_clause.simps Bex_def[symmetric]
    by presburger
  thus ?thesis
    unfolding ppprdefs comp_def Ball_def[symmetric]
            cnf_semantics_def clause_semantics_def validate_formula.simps
    unfolding ball_simps
    by presburger
qed

lemma pppr_ivcf: "cnf_semantics \<A> (ppcnf_of_prform S) = validate_formula (printerp_of_ppval \<A>) S"
  unfolding pppr_vicf[symmetric]
  unfolding ppval_of_printerp_def printerp_of_ppval_def
  by simp

lemma pppr_ivfc: "validate_formula (printerp_of_ppval \<A>) (prform_of_ppcnf C) = cnf_semantics \<A> C"
proof -
  have "pplit_of_prlit (prlit_of_pplit x) = x" for x
    by(cases x; simp)
  thus ?thesis
    unfolding pppr_vicf[symmetric]
    unfolding ppval_of_printerp_def printerp_of_ppval_def
    unfolding ppprdefs comp_def image_comp
    by simp
qed

lemma pppr_vifc: "validate_formula I (prform_of_ppcnf C) = cnf_semantics (ppval_of_printerp I) C"
  using pppr_ivcf pppr_ivfc pppr_vicf by blast
  
