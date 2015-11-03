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

text {*
  Generalizes sync_trs to handle multiple nested transition sets.
*}

definition
  synchro :: "('st,'ev) Tr set \<Rightarrow> ('st,'ev) Tr set list \<Rightarrow> ('ev \<Rightarrow> 'ev option list) \<Rightarrow> ('st \<Rightarrow> 'st list \<Rightarrow> 'st) \<Rightarrow> ('st, 'ev) Tr set"
where
  "synchro ts tsl sync_ev sync_st \<equiv>
   { \<lparr> src = sync_st (src t) srcl,
       dst = sync_st (dst t) dstl,
       lbl = lbl t \<rparr>
     | t srcl dstl
     . t \<in> ts \<and> 
       (\<forall>i < length tsl.
           if sync_ev (lbl t) ! i = None then srcl!i = dstl!i
           else \<lparr> src = srcl!i, dst = dstl!i, lbl = the (sync_ev (lbl t) ! i) \<rparr> \<in> tsl!i) }"

text {*
  A variation on the previous definition, where the relation between the states of the involved components
  is a predicate. We could instantiate such predicate as a characterization of a list of projections of the
  state of the top-level component to the states of the individual components.
*}

definition
  synchro2 :: "('st,'ev) Tr set \<Rightarrow> ('st,'ev) Tr set list \<Rightarrow> ('ev \<Rightarrow> 'ev option list) \<Rightarrow> ('st \<Rightarrow> 'st list \<Rightarrow> bool) \<Rightarrow> ('st, 'ev) Tr set"
where
  "synchro2 ts tsl sync_ev sync_st \<equiv>
   { t \<in> ts . \<exists> srcl dstl. 
       sync_st (src t) srcl \<and> sync_st (dst t) dstl \<and>
       (\<forall>i < length tsl.
           if sync_ev (lbl t) ! i = None then srcl!i = dstl!i
           else \<lparr> src = srcl!i, dst = dstl!i, lbl = the (sync_ev (lbl t) ! i) \<rparr> \<in> tsl!i) }"
(*
  "synchro2 ts tsl sync_ev sync_st \<equiv>
   { t | t srcl dstl e
     . t \<in> ts \<and> sync_st (src t) srcl \<and> sync_st (dst t) dstl \<and>
       (\<forall> i . (0 \<le> i \<and> i < length tsl \<longrightarrow>
             ((sync_ev (lbl t) ! i = None \<longrightarrow> srcl!i = dstl!i) \<and>
              (sync_ev (lbl t) ! i = Some e \<longrightarrow> 
                 \<lparr> src = srcl!i, dst = dstl!i, lbl = e \<rparr> \<in> tsl!i)))) }"
*)

text {*
  This third definition is similar to the previous one. It defines a predicate that checks that
  some transition t correctly ``synchronizes'' a list of transitions (that of the inner components),
  given an event synchronization mapping, and a state mapping predicate.
*}

definition
  synchro3 :: "('st,'ev) Tr \<Rightarrow> ('st,'ev) Tr list \<Rightarrow> ('ev \<Rightarrow> 'ev option list) \<Rightarrow> ('st \<Rightarrow> 'st list \<Rightarrow> bool) \<Rightarrow> bool"
where
  "synchro3 t trl sync_ev sync_st \<equiv>
   sync_st (src t) (map src trl) \<and> sync_st (dst t) (map dst trl) \<and>
       (\<forall>i < length trl.
             (sync_ev (lbl t) ! i = None \<and> src (trl!i) = dst (trl!i)) \<or>
             sync_ev (lbl t) ! i = Some (lbl (trl!i)))"

text {*
  This fourth definition rephrases the previous one. Here the correspondence between states is
  more direct: it is a mapping.
*}

definition
  synchro4 :: "('st,'ev) Tr \<Rightarrow> ('st,'ev) Tr list \<Rightarrow> ('ev \<Rightarrow> 'ev option list) \<Rightarrow> ('st \<Rightarrow> 'st list) \<Rightarrow> bool"
where
  "synchro4 t trl sync_ev sync_st \<equiv>
   sync_st (src t) = (map src trl) \<and> sync_st (dst t) = (map dst trl) \<and>
       (\<forall>i < length trl.
             (sync_ev (lbl t) ! i = None \<and> src (trl!i) = dst (trl!i)) \<or>
             sync_ev (lbl t) ! i = Some (lbl (trl!i)))"

text {*
  Same as before, but with list_all2 instead of quantification.
*}

definition
  synchro5 :: "('st,'ev) Tr \<Rightarrow> ('st,'ev) Tr list \<Rightarrow> ('ev \<Rightarrow> 'ev option list) \<Rightarrow> ('st \<Rightarrow> 'st list) \<Rightarrow> bool"
where
  "synchro5 t trl sync_ev sync_st \<equiv>
   sync_st (src t) = (map src trl) \<and> sync_st (dst t) = (map dst trl) \<and>
       list_all2 (\<lambda> ei ti . (ei = None \<and> src ti = dst ti) \<or> ei = Some (lbl ti)) (sync_ev (lbl t)) trl"

end