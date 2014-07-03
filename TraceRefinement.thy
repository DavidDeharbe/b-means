theory TraceRefinement

imports Main LTS Simulation

begin

definition refines :: "('st, 'ev) LTS \<Rightarrow> ('st, 'ev) LTS \<Rightarrow> bool" (infixl "\<sqsupseteq>" 50) 
  where "lc \<sqsupseteq> la \<equiv> traces lc \<subseteq> traces la"

abbreviation is_refined_by :: "('st, 'ev) LTS \<Rightarrow> ('st, 'ev) LTS \<Rightarrow> bool" (infixl "\<sqsubseteq>" 50) 
  where "la \<sqsubseteq> lc \<equiv> lc \<sqsupseteq> la"

lemma refines_refl: "l \<sqsupseteq> l" unfolding refines_def by auto
  
lemma lts_refines_trans: "l1 \<sqsupseteq> l2 \<and> l2 \<sqsupseteq> l3 \<Longrightarrow>  l1 \<sqsupseteq> l3" 
  unfolding refines_def by auto

(* TODO relate simulation and trace containment *)
lemma "(l1 :: ('st, 'ev) LTS) \<sim> l2 \<Longrightarrow> \<forall> r2 \<in> runs l2 . \<exists> r . \<exists> r1 \<in> runs l1 . simulate_run r r2 r1"
sorry

theorem "l1 \<sim> l2 \<Longrightarrow> l1 \<sqsubseteq> l1"
sorry

end
