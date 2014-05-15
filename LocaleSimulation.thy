theory LocaleSimulation

imports Main LocaleLTS

begin
section {* Behaviour: a set of traces *}

text {* We introduce the notion of simulation: a relation between the states of one LTS
and the states of another LTS such that any transition taken by the former can be simulated
by the latter, i.e. the latter can follow a transition that is labeled with the same event,
and leads to a state where it can continue the simulation: *}

locale Simulation =
  abstract: LTS asrc adst aevt ainit atrans
+ concrete: LTS csrc cdst cevt cinit ctrans
for
  asrc :: "'atrans \<Rightarrow> 'astate" and
  adst :: "'atrans \<Rightarrow> 'astate" and
  aevt :: "'atrans \<Rightarrow> 'event" and
  ainit :: "'astate set" and
  atrans :: "'atrans set" and
  csrc :: "'ctrans \<Rightarrow> 'cstate" and
  cdst :: "'ctrans \<Rightarrow> 'cstate" and
  cevt :: "'ctrans \<Rightarrow> 'event" and
  cinit :: "'cstate set" and
  ctrans :: "'ctrans set"
+
fixes
  r :: "('astate \<times> 'cstate) set"
assumes
  rinit: "\<forall> cs \<in> cinit . \<exists> as \<in> ainit . (as, cs) \<in> r" and
  rtrans: "\<forall> as cs . (as, cs) \<in> r \<longrightarrow> (\<forall> ct \<in> ctrans . csrc ct = cs \<longrightarrow>
              (\<exists> at \<in> atrans . asrc at = as \<and> aevt at = cevt ct \<and> (adst at, cdst ct) \<in> r))"
begin
end

sublocale LTS \<subseteq>
          Simulation src dst evt init trans 
                     src dst evt init trans
                     Id
by unfold_locales auto

locale SimulationComposition =
  sim1: Simulation asrc adst aevt ainit atrans msrc mdst mevt minit mtrans r1
+ sim2: Simulation msrc mdst mevt minit mtrans csrc cdst cevt cinit ctrans r2
for
  asrc :: "'atrans \<Rightarrow> 'astate" and
  adst :: "'atrans \<Rightarrow> 'astate" and
  aevt :: "'atrans \<Rightarrow> 'event" and
  ainit :: "'astate set" and
  atrans :: "'atrans set" and
  msrc :: "'mtrans \<Rightarrow> 'mstate" and
  mdst :: "'mtrans \<Rightarrow> 'mstate" and
  mevt :: "'mtrans \<Rightarrow> 'event" and
  minit :: "'mstate set" and
  mtrans :: "'mtrans set" and
  r1 :: "('astate \<times> 'mstate) set" and
  csrc :: "'ctrans \<Rightarrow> 'cstate" and
  cdst :: "'ctrans \<Rightarrow> 'cstate" and
  cevt :: "'ctrans \<Rightarrow> 'event" and
  cinit :: "'cstate set" and
  ctrans :: "'ctrans set" and
  r2 :: "('mstate \<times> 'cstate) set"

sublocale SimulationComposition \<subseteq> 
          Simulation asrc adst aevt ainit atrans
                     csrc cdst cevt cinit ctrans
                     "r1 O r2"
proof 
  from sim1.rinit sim2.rinit show "\<forall> cs \<in> cinit. \<exists> as \<in> ainit. (as, cs) \<in> r1 O r2"
    unfolding relcomp_unfold by simp metis
next
  from sim1.rtrans sim2.rtrans 
  show "\<forall>as cs. (as, cs) \<in> r1 O r2 \<longrightarrow> 
         (\<forall>ct\<in>ctrans. csrc ct = cs \<longrightarrow> 
           (\<exists>at\<in>atrans. asrc at = as \<and> aevt at = cevt ct \<and> (adst at, cdst ct) \<in> r1 O r2))"
    unfolding relcomp_unfold by simp metis
qed

text {* Based on the notion of simulation, we introduce the relation simulates on LTS: *}

locale Simulate =
  abstract: LTS asrc adst aevt ainit atrans
+ concrete: LTS csrc cdst cevt cinit ctrans
+ sim: Simulation asrc adst aevt ainit atrans csrc cdst cevt cinit ctrans r
for
  asrc :: "'atrans \<Rightarrow> 'astate" and
  adst :: "'atrans \<Rightarrow> 'astate" and
  aevt :: "'atrans \<Rightarrow> 'event" and
  ainit :: "'astate set" and
  atrans :: "'atrans set" and
  csrc :: "'ctrans \<Rightarrow> 'cstate" and
  cdst :: "'ctrans \<Rightarrow> 'cstate" and
  cevt :: "'ctrans \<Rightarrow> 'event" and
  cinit :: "'cstate set" and
  ctrans :: "'ctrans set" and
  r :: "('astate \<times> 'cstate) set"
begin
end

sublocale LTS \<subseteq> 
          Simulate src dst evt init trans
                   src dst evt init trans
                   Id
by unfold_locales auto

locale SimulateTransitive =
  sim1: Simulate asrc adst aevt ainit atrans msrc mdst mevt minit mtrans r1
+ sim2: Simulate msrc mdst mevt minit mtrans csrc cdst cevt cinit ctrans r2
for
  asrc :: "'atrans \<Rightarrow> 'astate" and
  adst :: "'atrans \<Rightarrow> 'astate" and
  aevt :: "'atrans \<Rightarrow> 'event" and
  ainit :: "'astate set" and
  atrans :: "'atrans set" and
  msrc :: "'mtrans \<Rightarrow> 'mstate" and
  mdst :: "'mtrans \<Rightarrow> 'mstate" and
  mevt :: "'mtrans \<Rightarrow> 'event" and
  minit :: "'mstate set" and
  mtrans :: "'mtrans set" and
  r1 :: "('astate \<times> 'mstate) set" and
  csrc :: "'ctrans \<Rightarrow> 'cstate" and
  cdst :: "'ctrans \<Rightarrow> 'cstate" and
  cevt :: "'ctrans \<Rightarrow> 'event" and
  cinit :: "'cstate set" and
  ctrans :: "'ctrans set" and
  r2 :: "('mstate \<times> 'cstate) set"

sublocale SimulateTransitive \<subseteq> 
          SimulationComposition
                   asrc adst aevt ainit atrans msrc mdst mevt minit mtrans r1
                   csrc cdst cevt cinit ctrans r2
by unfold_locales

sublocale SimulateTransitive \<subseteq> 
          Simulate asrc adst aevt ainit atrans
                   csrc cdst cevt cinit ctrans
                   "r1 O r2"
by unfold_locales

end
