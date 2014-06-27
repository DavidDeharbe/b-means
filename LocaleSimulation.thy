theory LocaleSimulation
imports Main LocaleLTS
begin
section {* Simulation *}

text {* We introduce the notion of simulation: a relation between the states of one LTS
and the states of another LTS such that any transition taken by the former can be simulated
by the latter, i.e. the latter can follow a transition that is labeled with the same event,
and leads to a state where it can continue the simulation: *}

locale Simulation =
  abstract: LTS la 
+ 
  concrete: LTS lc
for 
  la :: "('a, 'ev) LTS" and  lc :: "('c, 'ev) LTS"
+ 
fixes
  r :: "('a \<times> 'c) set"
assumes
  rinit: "\<forall> cs \<in> init lc. \<exists> as \<in> init la. (as, cs) \<in> r" and
  rtrans: "\<forall> as cs . (as, cs) \<in> r \<longrightarrow> (\<forall> ct \<in> trans lc. src ct = cs \<longrightarrow>
              (\<exists> at \<in> trans la. src at = as \<and> lbl at = lbl ct \<and> (dst at, dst ct) \<in> r))"
begin
end

text {* One simple property involving simulations is that the identity relation $Id$
defines a simulation of an LTS $l$by itself. This is expressed and showed in a context
containing the definition of LTS, as follows: *}
sublocale LTS \<subseteq>
          Simulation lts lts Id
by unfold_locales auto

locale SimulationComposition =
  sim1: Simulation la lb r1 + sim2: Simulation lb lc r2
for
  la :: "('a, 'ev) LTS" and lb :: "('b, 'ev) LTS" and lc :: "('c, 'ev) LTS" and
  r1 :: "('a \<times> 'b) set" and r2 :: "('b \<times> 'c) set"
begin
end

sublocale SimulationComposition \<subseteq> 
          Simulation la lc "r1 O r2"
proof 
  from sim1.rinit sim2.rinit show "\<forall> cs \<in> init lc. \<exists> as \<in> init la. (as, cs) \<in> r1 O r2"
    unfolding relcomp_unfold by simp metis
next
  from sim1.rtrans sim2.rtrans 
  show "\<forall>as cs. (as, cs) \<in> r1 O r2 \<longrightarrow> 
         (\<forall> ct \<in> trans lc. src ct = cs \<longrightarrow> 
           (\<exists> at \<in> trans la. src at = as \<and> lbl at = lbl ct \<and> (dst at, dst ct) \<in> r1 O r2))"
    unfolding relcomp_unfold by simp metis
qed

text {* We introduce the relation simulates on LTS. Is there a way to use the locale Simulation
in this definition? *}

locale Simulate =
  abstract: LTS la + concrete: LTS lc
for
  la :: "('a, 'ev) LTS" and lc :: "('c, 'ev) LTS"
+
assumes
  "\<exists> r . ((\<forall> cs \<in> init lc. \<exists> as \<in> init la. (as, cs) \<in> r) \<and>
          (\<forall> as cs . (as, cs) \<in> r \<longrightarrow> (\<forall> ct \<in> trans lc. src ct = cs \<longrightarrow>
              (\<exists> at \<in> trans la. src at = as \<and> lbl at = lbl ct \<and> (dst at, dst ct) \<in> r))))"
begin
end

sublocale Simulation \<subseteq> Simulate la lc
sorry
  
sublocale LTS \<subseteq> Simulate l l
by unfold_locales auto

locale SimulateCompose =
  sim1: Simulate la lb + sim2: Simulate lb lc
for
  la :: "('a, 'ev) LTS" and lb :: "('b, 'ev) LTS" and
  lc :: "('c, 'ev) LTS"
begin
end

sublocale SimulateCompose \<subseteq> Simulate la lc
sorry

end
