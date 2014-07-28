theory TraceRefinement

imports Main Simulation

begin

definition refines :: "('st, 'ev) LTS \<Rightarrow> ('st, 'ev) LTS \<Rightarrow> bool" (infixl "\<sqsupseteq>" 50) 
  where "lc \<sqsupseteq> la \<equiv> traces lc \<subseteq> traces la"

abbreviation is_refined_by :: "('st, 'ev) LTS \<Rightarrow> ('st, 'ev) LTS \<Rightarrow> bool" (infixl "\<sqsubseteq>" 50) 
  where "la \<sqsubseteq> lc \<equiv> lc \<sqsupseteq> la"

lemma refines_refl: "l \<sqsupseteq> l" unfolding refines_def by auto
  
lemma lts_refines_trans: "\<lbrakk>l \<sqsupseteq> l'; l' \<sqsupseteq> l''\<rbrakk> \<Longrightarrow> l \<sqsupseteq> l''" 
  unfolding refines_def by auto

lemma 
  assumes "l \<sim> l'" "ts' \<in> runs l'"
  obtains r ts where "ts \<in> runs l" "sim_run r ts' ts"
  using assms unfolding simulates_def by (metis sim_run)

theorem "l \<sim> l' \<Longrightarrow> l \<sqsubseteq> l'" 
  unfolding simulates_def refines_def by (metis sim_trace_inclusion)

end
