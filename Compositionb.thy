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

text {*
  Part of the behavior of a LTS may be realized by another, imported, LTS. Record Import models such
  relationship. Its first field is the imported LTS. The second field specifies how the state of
  the importing and imported LTS are related, i.e. by means of a function from states (of the
  importing LTS) to states (of the imported LTS). One can view such function as a projection.
  The third and last field specifies whether an event of the importing LTS is associated with an event 
  of the imported LTS. Notice that there is no field to represent the importing LTS. Import records
  will always be used in contexts where this LTS is available.

  The type for these relationships between states and events is directed by the characteristics of
  the B construct "IMPORTS". The state of the importing component is composed of the value of the
  state variables and of the state of the imported components. An operation of an importing component
  may use at most one operation of each imported component.

  Notice that nothing in the formalization prevents to associate several Import records to the
  same LTS.
*}
record ('st, 'ev) Import =
  lts :: "('st, 'ev) LTS"         -- "imported LTS"
  sync_st :: "'st \<Rightarrow> 'st"         -- "state projection"
  sync_ev :: "'ev \<Rightarrow> 'ev option"  -- "event called from the imported LTS"

text {*
  Next we specify soundness conditions for an import of a LTS B, with respect to a given importing 
  LTS A.
  First, the projection of every initial state of A is an initial state in B.
  Second, for each transition t of A, either it is not associated with an event of B, or it is 
  associated to some event e of B. In that case, there must
  be a transition in B labeled with e, such that the source and destination
  states are state projections of the end states of the transition t.
*}
definition
  sound_import :: "('st,'ev) LTS \<Rightarrow> ('st,'ev) Import \<Rightarrow> bool"
where
  "sound_import A import \<equiv>
    (let (B, proj, sync) = (lts import, sync_st import, sync_ev import) in
    proj ` (init A) \<subseteq> (init B) \<and>
    (\<forall>t . t \<in> (trans A) \<longrightarrow> 
      (case sync (lbl t) of
         None \<Rightarrow> proj (src t) = proj (dst t)
       | Some e \<Rightarrow> \<lparr> src = src t, dst = dst t, lbl = e \<rparr> \<in> trans B)))"

text {*
  Suppose LTS A imports LTS B. We want to show that, for every run of A, the interactions between 
  A and B correspond to a run of B. We first give an auxiliary definition, that map 
  lists of pairs of states and events of A to corresponding lists in B.
*}
primrec
  interaction_trns :: "('st, 'ev) LTS \<Rightarrow> ('st, 'ev) Import \<Rightarrow> ('st \<times> 'ev) list \<Rightarrow> ('st \<times> 'ev) list"
where
  "interaction_trns A import [] = []" |
  "interaction_trns A import (x # xs) =
    (case (sync_ev import) (snd x) of
       None \<Rightarrow> interaction_trns A import xs |
       Some e \<Rightarrow> ((sync_st import) (fst x), e) # (interaction_trns A import xs))"

text {*
  We can now define the desired function. It takes as input an LTS A, an import, a run of A and
  yields a run of the imported LTS.
*}
definition
  interaction :: "('st, 'ev) LTS \<Rightarrow> ('st, 'ev) Import \<Rightarrow> ('st, 'ev) Run \<Rightarrow> ('st, 'ev) Run"
where
  "interaction ltsa import run \<equiv>
    \<lparr> trns = interaction_trns ltsa import (trns run), fins = (sync_st import) (fins run) \<rparr>"

text {*
  Next are enunciated two potentially interesting theorems. The first theorem states that
  for every run of A, giving rise to a run r', then r' is indeed a run of the imported LTS
*}

theorem interaction_runs
  "\<lbrakk> r \<in> runs A; interaction A import r = r' \<rbrakk> \<Longrightarrow> r' \<in> runs (lts import)"
sorry

text {*
  The second theorem states that every reachable state of A projects to a reachable state of
  the imported LTS.
*}

theorem import_reachable
  "\<lbrakk> s \<in> states A; sound_import A import \<rbrakk> \<Longrightarrow> (sync_st import) s \<in> states (lts import)"
sorry


end