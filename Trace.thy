theory Trace

imports Main LTS Simulation

begin

type_synonym RUN = "TRANSITION list"
type_synonym TRACE = "EVENT list"

inductive_set wf_runs :: "TRANSITION set \<Rightarrow> RUN set" for S :: "TRANSITION set" where
  base : "[] \<in> wf_runs S"
| step : "\<lbrakk> r \<in> wf_runs S; t \<in> S; src t = dst (last r) \<rbrakk> \<Longrightarrow> (r @ [ t ]) \<in> wf_runs S"

definition traces :: "LTS \<Rightarrow> TRACE set" where
  "traces l \<equiv> { map evt r | r . r \<in> wf_runs (trans l) \<and> (r \<noteq> [] \<longrightarrow> src(hd r) \<in> init l) }"

definition refines :: "LTS \<Rightarrow> LTS \<Rightarrow> bool" (infixl "\<sqsupseteq>" 50) where
  "refines lc la \<equiv> traces lc \<subseteq> traces la"

lemma refines_refl: "l \<sqsupseteq> l" unfolding refines_def by auto
  
lemma lts_refines_trans: "l1 \<sqsupseteq> l2 \<and> l2 \<sqsupseteq> l3 \<Longrightarrow>  l1 \<sqsupseteq> l3" 
  unfolding refines_def by auto

(* TODO relate simulation and trace containment *)

end
