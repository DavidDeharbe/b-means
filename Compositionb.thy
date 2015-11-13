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
  Generalizes @{text "sync_trs"} to handle multiple nested transition sets.
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
  Same as before, but with @{text "list_all2"} instead of quantification.
*}

definition
  synchro5 :: "('st,'ev) Tr \<Rightarrow> ('st,'ev) Tr list \<Rightarrow> ('ev \<Rightarrow> 'ev option list) \<Rightarrow> ('st \<Rightarrow> 'st list) \<Rightarrow> bool"
where
  "synchro5 t trl sync_ev sync_st \<equiv>
   sync_st (src t) = (map src trl) \<and> sync_st (dst t) = (map dst trl) \<and>
       list_all2 (\<lambda> ei ti . (ei = None \<and> src ti = dst ti) \<or> ei = Some (lbl ti)) (sync_ev (lbl t)) trl"

text {*
  Part of the behavior of a LTS may be realized by another, included, LTS. Record Includes models such
  relationship. Its first field is the included LTS. The second field specifies how the state of
  the including and included LTS are related, i.e. by means of a function from states (of the
  including LTS) to states (of the included LTS). One can view such function as a projection.
  The third and last field specifies whether an event of the including LTS is associated with an event 
  of the included LTS. Notice that there is no field to represent the including LTS. Import records
  will always be used in contexts where this LTS is available.

  The type for these relationships between states and events is directed by the characteristics of
  the B construct ``IMPORTS''. The state of the including component is composed of the value of the
  state variables and of the state of the included components. An operation of an including component
  may use at most one operation of each included component.

  Notice that nothing in the formalization prevents associating several Import records to the
  same LTS.
*}
record ('st, 'ev) Includes =
  lts :: "('st, 'ev) LTS"         -- "included LTS"
  sync_st :: "'st \<Rightarrow> 'st"         -- "state projection"
  sync_ev :: "'ev \<Rightarrow> 'ev option"  -- "event called from the included LTS"

text {*
  Next we specify soundness conditions for an inclusion of a LTS B, with respect to a given 
  including LTS A.
  First, the projection of every initial state of A is an initial state in B.
  Second, for each transition t of A, either it is not associated with an event of B, or it is 
  associated to some event e of B. In that case, there must
  be a transition in B labeled with e, such that the source and destination
  states are state projections of the end states of the transition t.
*}
definition
  sound_includes :: "('st,'ev) LTS \<Rightarrow> ('st,'ev) Includes \<Rightarrow> bool"
where
  "sound_includes A included \<equiv>
    (let (B, proj, sync) = (lts included, sync_st included, sync_ev included) in
    proj ` (init A) \<subseteq> (init B) \<and>
    (\<forall>t \<in> trans A. 
      (case sync (lbl t) of
         None \<Rightarrow> proj (src t) = proj (dst t)
       | Some e \<Rightarrow> \<lparr> src = proj(src t), dst = proj(dst t), lbl = e \<rparr> \<in> trans B)))"

text {*
  Suppose LTS A includes LTS B. We want to show that, for every run of A, the interactions between 
  A and B correspond to a run of B. We first give an auxiliary definition, that maps 
  lists of pairs of states and events of A to corresponding lists in B.
*}
definition
  interaction_trns :: "('st, 'ev) LTS \<Rightarrow> ('st, 'ev) Includes \<Rightarrow> ('st \<times> 'ev) list \<Rightarrow> ('st \<times> 'ev) list"
where
  "interaction_trns A included lst = 
  map (\<lambda>(s,ev). (sync_st included s, the (sync_ev included ev)))
      (filter (\<lambda>(s,ev). sync_ev included ev \<noteq> None) lst)"

text {*
  We can now define the desired function. It takes as input an LTS A, an Includes, a run of A and
  yields a run of the included LTS.
*}
definition
  interaction :: "('st, 'ev) LTS \<Rightarrow> ('st, 'ev) Includes \<Rightarrow> ('st, 'ev) Run \<Rightarrow> ('st, 'ev) Run"
where
  "interaction ltsa included run \<equiv>
    \<lparr> trns = interaction_trns ltsa included (trns run), 
      fins = sync_st included (fins run) \<rparr>"

text {*
  Next are enunciated some potentially interesting theorems. The first theorem states that
  for every reachable state s of A, for a given sound Includes of A, the projection of s on the
  included LTS is reachable.
*}
theorem interaction_states:
assumes s: "s \<in> states A" and imp: "sound_includes A included"
  shows "(sync_st included) s \<in> states (lts included)"
using s
proof(induct s)
  fix s
  assume "s \<in> init A" 
  with imp show "sync_st included s \<in> states (lts included)"
    unfolding sound_includes_def by auto
next
  fix s t
  assume ih: "(sync_st included) s \<in> states (lts included)"
     and t: "t \<in> outgoing A s"
  show "sync_st included (dst t) \<in> states (lts included)"
  proof(cases "sync_ev included (lbl t)")
    case None
    with t ih imp show ?thesis
      unfolding sound_includes_def outgoing_def by auto
  next
    fix a
    assume a: "sync_ev included (lbl t) = Some a" 
    let ?t = "\<lparr> src = sync_st included s, dst = sync_st included (dst t), lbl = a \<rparr>"
    from t imp a have "?t \<in> outgoing (lts included) (sync_st included s)"
      unfolding outgoing_def sound_includes_def by auto
    with ih show  "sync_st included (dst t) \<in> states (lts included)"
      by (auto dest: states.step)
  qed
qed

text {*
  The second theorem extends the result of the previous theorem to runs.
*}
theorem interaction_runs:
assumes r: "r \<in> runs A" and imp: "sound_includes A included"
  shows "interaction A included r \<in> runs (lts included)"
using r proof (induct)
  fix s
  assume "s \<in> init A"
  with imp have "sync_st included s \<in> init (lts included)"
    unfolding sound_includes_def by auto
  thus "interaction A included \<lparr>trns = [], fins = s\<rparr> \<in> runs (lts included)"
    unfolding interaction_def interaction_trns_def by (auto intro: runs.start)
next
  fix run t
  assume ih: "interaction A included run \<in> runs (lts included)"
     and t: "t \<in> outgoing A (fins run)"

  show "interaction A included (append_tr run t) \<in> runs (lts included)"
  proof (cases "sync_ev included (lbl t)")
    case None
    hence "interaction_trns A included (trns (append_tr run t)) =
           interaction_trns A included (trns run)"
      unfolding interaction_trns_def append_tr_def by auto
    moreover
    from None imp t
    have "sync_st included (fins (append_tr run t)) = sync_st included (fins run)"
      unfolding sound_includes_def outgoing_def append_tr_def by auto
    ultimately
    show ?thesis using ih unfolding interaction_def by simp
  next
    fix a
    assume a: "sync_ev included (lbl t) = Some a"
    let ?s = "fins run"
    let ?t = "\<lparr> src = sync_st included ?s, dst = sync_st included (dst t), lbl = a \<rparr>"
    from t imp a have "?t \<in> outgoing (lts included) (sync_st included ?s)"
      unfolding outgoing_def sound_includes_def by auto
    moreover
    have "sync_st included ?s = fins (interaction A included run)"
      unfolding interaction_def by simp
    ultimately
    have "append_tr (interaction A included run) ?t \<in> runs (lts included)"
      using ih by (auto dest: runs.step)
    moreover
    from a have "interaction A included (append_tr run t) =
                 append_tr (interaction A included run) ?t"
      unfolding interaction_def interaction_trns_def append_tr_def
      by auto
    ultimately show ?thesis by simp
  qed
qed

text {*
  This result is now lifted to the level of traces (observable behavior).
*}
theorem interaction_traces:
assumes tr: "tr \<in> traces A" and imp: "sound_includes A included"
  shows "map (the o sync_ev included) (filter (\<lambda>e. sync_ev included e \<noteq> None) tr)
         \<in> traces (lts included)"   (is "?tr \<in> _")
proof -
  from tr obtain run where run: "run \<in> runs A" "tr = trace_of run"
    unfolding traces_def by auto
  from `run \<in> runs A` imp have "interaction A included run \<in> runs (lts included)"
    by (blast dest: interaction_runs)
  hence "trace_of (interaction A included run) \<in> traces (lts included)"
    unfolding traces_def by auto
  moreover
  from `tr = trace_of run`
  have 1: "filter (\<lambda>e. sync_ev included e \<noteq> None) tr =
           map snd (filter ((\<lambda>e. sync_ev included e \<noteq> None) o snd) (trns run))"
    unfolding trace_of_def by (auto simp: filter_map)
   have 2: "(\<lambda>e. sync_ev included e \<noteq> None) o snd =
            (\<lambda>(s,ev). sync_ev included ev \<noteq> None)"
    by auto
  from 1 2 have "filter (\<lambda>e. sync_ev included e \<noteq> None) tr =
           map snd (filter (\<lambda>(s,ev). sync_ev included ev \<noteq> None) (trns run))"
    by metis
  hence "?tr = trace_of (interaction A included run)"
    unfolding interaction_def interaction_trns_def trace_of_def
    by auto
  ultimately show ?thesis by simp
qed

end