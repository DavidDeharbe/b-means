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
       | Some e \<Rightarrow> \<lparr> src = proj(src t), dst = proj(dst t), lbl = e \<rparr> \<in> trans B)))"

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

lemma app_interaction_trns:
"interaction_trns A import (xs @ [x]) =
  (case (sync_ev import) (snd x) of
    None \<Rightarrow> interaction_trns A import xs |
    Some e \<Rightarrow> (interaction_trns A import xs) @ [(sync_st import (fst x), e)])"
proof(cases "sync_ev import (snd x)")
  assume "sync_ev import (snd x) = None"
  then show "interaction_trns A import (xs @ [x]) =
    (case sync_ev import (snd x) of None \<Rightarrow> interaction_trns A import xs
     | Some e \<Rightarrow> interaction_trns A import xs @ [(sync_st import (fst x), e)])"
  proof(induct xs)
    assume "sync_ev import (snd x) = None"
    then show "interaction_trns A import ([] @ [x]) =
    (case sync_ev import (snd x) of None \<Rightarrow> interaction_trns A import []
     | Some e \<Rightarrow> interaction_trns A import [] @ [(sync_st import (fst x), e)])"
    using interaction_trns.simps by simp
  next
    fix a xs
    assume 0: "sync_ev import (snd x) = None \<Longrightarrow>
             interaction_trns A import (xs @ [x]) =
             (case sync_ev import (snd x) of None \<Rightarrow> interaction_trns A import xs
              | Some e \<Rightarrow> interaction_trns A import xs @ [(sync_st import (fst x), e)])"
      and 1: "sync_ev import (snd x) = None"
    then have 2: "interaction_trns A import (xs @ [x]) =
             (case sync_ev import (snd x) of None \<Rightarrow> interaction_trns A import xs
              | Some e \<Rightarrow> interaction_trns A import xs @ [(sync_st import (fst x), e)])" by simp
    with 1 interaction_trns.simps
      show "interaction_trns A import ((a # xs) @ [x]) =
              (case sync_ev import (snd x) of None \<Rightarrow> interaction_trns A import (a # xs)
               | Some e \<Rightarrow> interaction_trns A import (a # xs) @ [(sync_st import (fst x), e)])" 
      by (simp add: option.case_eq_if)
  qed
next
  fix a
  assume "sync_ev import (snd x) = Some a"
  then show "interaction_trns A import (xs @ [x]) =
         (case sync_ev import (snd x) of None \<Rightarrow> interaction_trns A import xs
          | Some e \<Rightarrow> interaction_trns A import xs @ [(sync_st import (fst x), e)])"
  proof(induct xs)
    assume "sync_ev import (snd x) = Some a"
    then show "interaction_trns A import ([] @ [x]) =
    (case sync_ev import (snd x) of None \<Rightarrow> interaction_trns A import []
     | Some e \<Rightarrow> interaction_trns A import [] @ [(sync_st import (fst x), e)])"
    using interaction_trns.simps by simp
  next
    fix aa xs
    assume ih: "sync_ev import (snd x) = Some a \<Longrightarrow>
              interaction_trns A import (xs @ [x]) =
              (case sync_ev import (snd x) of None \<Rightarrow> interaction_trns A import xs
               | Some e \<Rightarrow> interaction_trns A import xs @ [(sync_st import (fst x), e)])"
       and ev: " sync_ev import (snd x) = Some a"
    then show "interaction_trns A import ((aa # xs) @ [x]) =
             (case sync_ev import (snd x) of None \<Rightarrow> interaction_trns A import (aa # xs)
              | Some e \<Rightarrow> interaction_trns A import (aa # xs) @ [(sync_st import (fst x), e)])"
      using interaction_trns.simps
      by (simp add: option.case_eq_if)
  qed
qed

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
  Next are enunciated some potentially interesting theorems. The first theorem states that
  for every reachable state s of A, for a given sound import of A, the projection of s on the
  imported LTS is reachable.
*}
sledgehammer_params[provers="z3 cvc4 remote_vampire e spass"]
theorem interaction_states:
assumes "s \<in> states A"
    and "sound_import A import"
  shows "(sync_st import) s \<in> states (lts import)"
using assms
proof(induction s)
  fix s
  assume "s \<in> init A" and "sound_import A import" 
  then show "sync_st import s \<in> states (lts import)" unfolding sound_import_def by auto
next
  fix s t
  show "s \<in> states A \<Longrightarrow>
           (sound_import A import \<Longrightarrow> sync_st import s \<in> states (lts import)) \<Longrightarrow>
           t \<in> outgoing A s \<Longrightarrow> sound_import A import \<Longrightarrow> sync_st import (dst t) \<in> states (lts import)"
  proof(cases "(sync_ev import) (lbl t)")
    assume h0: "s \<in> states A"
       and h1: "(sound_import A import \<Longrightarrow> sync_st import s \<in> states (lts import))" 
       and h2: "t \<in> outgoing A s"
       and h3: "sound_import A import"
       and h4: "sync_ev import (lbl t) = None" 
    then have "sync_st import s \<in> states (lts import)" by simp
    with h0 h2 h3 h4 show "sync_st import (dst t) \<in> states (lts import)"
      unfolding sound_import_def outgoing_def by auto
  next
    fix a
    assume s: "s \<in> states A"
       and ih: "(sound_import A import \<Longrightarrow> sync_st import s \<in> states (lts import))" 
       and t: "t \<in> outgoing A s"
       and sound: "sound_import A import"
       and sync: "sync_ev import (lbl t) = Some a" 
    let ?t = "\<lparr> src = (sync_st import) (src t), dst = (sync_st import) (dst t), lbl = a \<rparr>"
    from s t sound sync have "?t \<in> trans (lts import)" unfolding outgoing_def sound_import_def by auto
    then have outgoing: "?t \<in> outgoing (lts import) ((sync_st import) (src t))" unfolding outgoing_def by auto
    from ih sound s t have "sync_st import (src t) \<in> states (lts import)" unfolding outgoing_def by simp
    with outgoing show  "sync_st import (dst t) \<in> states (lts import)" using states.step by fastforce
  qed
qed

text {*
  The second theorem extends the result of the previous theorem to runs.
*}
theorem interaction_runs:
assumes "r \<in> runs A"
    and "sound_import A import"
  shows "interaction A import r \<in> runs (lts import)"
using assms unfolding interaction_def
proof(induct r)
  fix s
  assume s: "s \<in> init A"
     and sound: "sound_import A import"
    with runs.start have "\<lparr>trns = [], fins = sync_st import s\<rparr> \<in> runs (lts import)" 
      unfolding sound_import_def by (metis (no_types, lifting) image_subset_iff splitD)
    then show "\<lparr>trns = interaction_trns A import (trns \<lparr>trns = [], fins = s\<rparr>), fins = sync_st import (fins \<lparr>trns = [], fins = s\<rparr>)\<rparr> \<in> runs (lts import)" by simp
next
  fix run t
  show "run \<in> runs A \<Longrightarrow>
        (sound_import A import \<Longrightarrow>
           \<lparr>trns = interaction_trns A import (trns run), fins = sync_st import (fins run)\<rparr> \<in> runs (lts import)) \<Longrightarrow>
        t \<in> outgoing A (fins run) \<Longrightarrow>
        sound_import A import \<Longrightarrow>
        \<lparr>trns = interaction_trns A import (trns (append_tr run t)), fins = sync_st import (fins (append_tr run t))\<rparr>
          \<in> runs (lts import) "
    proof(cases "sync_ev import (lbl t)")
      assume 0: "run \<in> runs A"
         and 1: "sound_import A import \<Longrightarrow> \<lparr>trns = interaction_trns A import (trns run), fins = sync_st import (fins run)\<rparr> \<in> runs (lts import)"
         and 2: "t \<in> outgoing A (fins run)"
         and 3: "sound_import A import"
         and 4: "sync_ev import (lbl t) = None"
     from 1 3 have 5: "\<lparr>trns = interaction_trns A import (trns run), fins = sync_st import (fins run)\<rparr> \<in> runs (lts import)" by simp
     from 2 3 4 have 6: "sync_st import (fins run) = sync_st import (fins (append_tr run t))" 
       unfolding sound_import_def append_tr_def outgoing_def by auto 
     from 2 trns_append_tr 
       have 7: "interaction_trns A import (trns (append_tr run t)) = interaction_trns A import (trns run @ [(src t, lbl t)])"
         unfolding outgoing_def by fastforce
     from 4
       have "interaction_trns A import (trns run  @ [(src t, lbl t)]) = interaction_trns A import (trns run)"
       using app_interaction_trns by (simp add: app_interaction_trns)
     with 5 6 7 runs.step show "\<lparr>trns = interaction_trns A import (trns (append_tr run t)), fins = sync_st import (fins (append_tr run t))\<rparr> \<in> runs (lts import)"
       by simp
   next
     fix a
      assume 0: "run \<in> runs A"
         and 1: "sound_import A import \<Longrightarrow> \<lparr>trns = interaction_trns A import (trns run), fins = sync_st import (fins run)\<rparr> \<in> runs (lts import)"
         and 2: "t \<in> outgoing A (fins run)"
         and 3: "sound_import A import"
         and 4: "sync_ev import (lbl t) = Some a" 
     show "\<lparr>trns = interaction_trns A import (trns (append_tr run t)), fins = sync_st import (fins (append_tr run t))\<rparr> \<in> runs (lts import)"
       sorry
   qed
qed

end