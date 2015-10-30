theory Compositionb
imports Simulationb
begin

(** Here's a polymorphic and symmetric version of composition.

definition
  sync_trs :: "('sa,'ea) Tr set \<Rightarrow> ('sb,'eb) Tr set \<Rightarrow> ('ea \<times> 'eb) set \<Rightarrow> ('sa \<times> 'sb, 'ea option \<times> 'eb option) Tr set"
where
  "sync_trs trsa trsb sync \<equiv>
   { \<lparr> src = (src tra, src trb), dst = (dst tra, dst trb), lbl = (Some (lbl tra), Some (lbl trb)) \<rparr>
     | tra trb . tra \<in> trsa \<and> trb \<in> trsb \<and> (lbl tra, lbl trb) \<in> sync } 
   \<union>
   { \<lparr> src = (src tra, sb), dst = (dst tra, sb), lbl = (Some (lbl tra), None) \<rparr>
     | tra sb . tra \<in> trsa \<and> \<not>(\<exists>eb. (lbl tra, eb) \<in> sync) } (* might require sb \<in> src ` trsb *)
   \<union>
   { \<lparr> src = (sa, src trb), dst = (sa, dst trb), lbl = (None, Some (lbl trb)) \<rparr>
     | sa trb . trb \<in> trsb \<and> \<not>(\<exists>ea. (ea, lbl trb) \<in> sync) }"

definition
  compose :: "('sa,'ea) LTS \<Rightarrow> ('sb,'eb) LTS \<Rightarrow> ('ea \<times> 'eb) set \<Rightarrow> ('sa \<times> 'sb, 'ea option \<times> 'eb option) LTS"
where
  "compose lta ltb sync \<equiv>
    \<lparr> init = init lta \<times> init ltb,
      trans = sync_trs (trans lta) (trans ltb) sync \<rparr>"

However, since simulation requires LTSs of the same type, we'll do it monomorphically.
Moreover, we define an asymmetric relation where the first LTS drives transitions,
possibly constrained by transitions of the second one. The transitions of the product
are labeled with the events of the first LTS. In particular, this will allow us to obtain
a simulation between the product and the first LTS.
**)

text {*
  A notion of synchronized composition of two LTSs. The idea is that transitions of
  the product are inherited from those of the first LTS, possibly constrained by
  transitions of the second one, as determined by a synchronization function. The
  states of the composed LTS are constructed from the states of the component LTSs
  through function @{text mkst}.
*}

definition
  sync_trs :: "('st,'ev) Tr set \<Rightarrow> ('st,'ev) Tr set \<Rightarrow> ('st \<Rightarrow> 'st \<Rightarrow> 'st) \<Rightarrow> ('ev \<Rightarrow> 'ev option) \<Rightarrow> ('st, 'ev) Tr set"
where
  "sync_trs trsa trsb mkst sync \<equiv>
   { \<lparr> src = mkst (src tra) (src trb), dst = mkst (dst tra) (dst trb), lbl = lbl tra \<rparr>
     | tra trb . tra \<in> trsa \<and> trb \<in> trsb \<and> sync (lbl tra) = Some (lbl trb) } 
   \<union>
   { \<lparr> src = mkst (src tra) sb, dst = mkst (dst tra) sb, lbl = lbl tra \<rparr>
     | tra sb . tra \<in> trsa \<and> sync (lbl tra) = None }" (* might require sb \<in> src ` trsb *)

definition
  compose :: "('st,'ev) LTS \<Rightarrow> ('st,'ev) LTS \<Rightarrow> ('st \<Rightarrow> 'st \<Rightarrow> 'st) \<Rightarrow> ('ev \<Rightarrow> 'ev option) \<Rightarrow> ('st, 'ev) LTS"
where
  "compose lta ltb mkst sync \<equiv>
    \<lparr> init = { mkst s t | s t . s \<in> init lta \<and> t \<in> init ltb },
      trans = sync_trs (trans lta) (trans ltb) mkst sync \<rparr>"

text {*
  The composition of two LTSs is simulated by the first original LTSs.
*}
lemma compose_sim_left:
  assumes inj: "\<And>sa sb sa' sb'. mkst sa sb = mkst sa' sb' \<Longrightarrow> sa = sa'"
  shows "(compose lta ltb mkst sync, lta) \<in> simulation {(mkst s t, s) | s t . True}"
  (is "(?comp, _) \<in> simulation ?r")
(* works, but takes very long ...
   using assms unfolding simulation_def compose_def sync_trs_def outgoing_def sim_transition_def
   apply fastforce *)
proof -
  {
    fix sc
    assume "sc \<in> init ?comp"
    hence "\<exists>s' \<in> init lta. (sc, s') \<in> ?r" unfolding compose_def by auto
  }
  moreover
  {
    fix sc sa t
    assume s: "(sc, sa) \<in> ?r" and t: "t \<in> outgoing ?comp sc"
    from s obtain sb where sb: "sc = mkst sa sb" by auto
    from t obtain tra sb' sb'' where 
      tra: "tra \<in> trans lta" "src t = sc" "sc = mkst (src tra) sb'" 
           "lbl t = lbl tra" "dst t = mkst (dst tra) sb''"
      unfolding outgoing_def compose_def sync_trs_def by auto
    with inj sb have "src tra = sa" by blast
    with tra sb have "\<exists>t' \<in> outgoing lta sa. (t,t') \<in> sim_transition ?r"
      unfolding outgoing_def sim_transition_def by auto
  }
  ultimately show ?thesis unfolding simulation_def by blast
qed

end