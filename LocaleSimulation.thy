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
  rinit: "\<forall>cs \<in> init lc. \<exists>as \<in> init la. (as, cs) \<in> r" and
  rtrans: "\<forall>as cs. (as, cs) \<in> r \<longrightarrow> (\<forall>ct \<in> trans lc. src ct = cs \<longrightarrow>
              (\<exists>at \<in> trans la. src at = as \<and> lbl at = lbl ct \<and> (dst at, dst ct) \<in> r))"
begin
end

text {* One simple property involving simulations is that the identity relation @{text "Id"}}
defines a simulation of an LTS @{text l} by itself. This is expressed and showed in a context
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
  from sim1.rinit sim2.rinit show "\<forall>cs \<in> init lc. \<exists>as \<in> init la. (as, cs) \<in> r1 O r2"
    unfolding relcomp_unfold by fastforce
next
  from sim1.rtrans sim2.rtrans 
  show "\<forall>as cs. (as, cs) \<in> r1 O r2 \<longrightarrow> 
         (\<forall>ct \<in> trans lc. src ct = cs \<longrightarrow> 
           (\<exists>at \<in> trans la. src at = as \<and> lbl at = lbl ct \<and> (dst at, dst ct) \<in> r1 O r2))"
    unfolding relcomp_unfold by fastforce
qed

text {* We introduce the relation simulates on LTS. Is there a way to use the locale Simulation
in this definition? *}

locale Simulate =
  abstract: LTS la + concrete: LTS lc
for
  la :: "('a, 'ev) LTS" and lc :: "('c, 'ev) LTS"
+
assumes
  rel: "\<exists>r. ((\<forall>cs \<in> init lc. \<exists>as \<in> init la. (as, cs) \<in> r) \<and>
          (\<forall>as cs. (as, cs) \<in> r \<longrightarrow> (\<forall>ct \<in> trans lc. src ct = cs \<longrightarrow>
              (\<exists>at \<in> trans la. src at = as \<and> lbl at = lbl ct \<and> (dst at, dst ct) \<in> r))))"
begin
end

sublocale Simulation \<subseteq> Simulate la lc
  using rinit rtrans by unfold_locales auto
  
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
proof
  from sim1.rel obtain rab where
    rab: "\<forall>bs \<in> init lb. \<exists>as \<in> init la. (as, bs) \<in> rab"
         "\<forall>as bs. (as, bs) \<in> rab \<longrightarrow> (\<forall>bt \<in> trans lb. src bt = bs \<longrightarrow>
              (\<exists>at \<in> trans la. src at = as \<and> lbl at = lbl bt \<and> (dst at, dst bt) \<in> rab))"
    by blast
  from sim2.rel obtain rbc where
    rbc: "\<forall>cs \<in> init lc. \<exists>bs \<in> init lb. (bs, cs) \<in> rbc"
         "\<forall>bs cs. (bs, cs) \<in> rbc \<longrightarrow> (\<forall>ct \<in> trans lc. src ct = cs \<longrightarrow>
              (\<exists>bt \<in> trans lb. src bt = bs \<and> lbl bt = lbl ct \<and> (dst bt, dst ct) \<in> rbc))"
    by blast
  from rab rbc show
    "\<exists>r. (\<forall>cs\<in>init lc. \<exists>as\<in>init la. (as, cs) \<in> r) \<and>
        (\<forall>as cs.
            (as, cs) \<in> r \<longrightarrow>
            (\<forall>ct\<in>trans lc.
                src ct = cs \<longrightarrow>
                (\<exists>at\<in>trans la.
                    src at = as \<and> lbl at = lbl ct \<and> (dst at, dst ct) \<in> r)))"
  by (intro exI[where x="rab O rbc"]) (fastforce simp: relcomp_unfold)
qed

end
