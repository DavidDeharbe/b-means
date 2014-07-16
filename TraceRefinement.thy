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

lemma "l1 \<sim> l2 \<Longrightarrow> \<forall> r2 \<in> runs l2 . \<exists> s . \<exists> r1 \<in> runs l1 . sim_run s r2 r1"
  unfolding simulates_def by (metis sim_run)

theorem "\<lbrakk> l1 \<sim> l2 \<rbrakk> \<Longrightarrow> l1 \<sqsubseteq> l2" 
  unfolding simulates_def refines_def by (metis sim_trace_inclusion)

end
