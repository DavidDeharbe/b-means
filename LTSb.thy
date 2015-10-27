theory LTSb

imports Main

begin

section {* Labeled transition systems and their executions *}

subsection {* Labeled transition systems *}

text {* 
  The semantics of a B component is a discrete, eventful, state-transition system. We 
  formalize labeled transition systems (LTS) and their behaviors, independently of B.
  An LTS is given by a set of initial states and a set of transitions, which are
  triples (source and destination state, and a transition label). The following
  definitions of transitions and transition systems are parameterized by types
  @{text "'st"} and @{text "'ev"} of states and events.
*}

record ('st, 'ev) Tr =
  src :: 'st     -- "source state"
  dst :: 'st     -- "destination state"
  lbl :: 'ev     -- "labeling event"

record ('st, 'ev) LTS =
  init :: "'st set" -- "set of initial states"
  trans :: "('st, 'ev) Tr set" -- "set of transitions"

text {*
   We first introduce auxiliary definitions for some useful
   concepts. The function @{text "outgoing"}, given a LTS and a
   state, returns the set of outgoing transitions in that state.  
*}

definition
  outgoing :: "('st, 'ev) LTS \<Rightarrow> 'st \<Rightarrow> ('st, 'ev) Tr set"
where
  "outgoing l \<equiv> \<lambda>s. { t \<in> trans l . src t = s}"

text {*
  The function @{text "accepted_events"}, given an LTS and a state,
  returns the set of events that label the outgoing transitions in
  that state. It corresponds to the operations and the corresponding
  parameter valuations that are applicable in that state.  
*}

definition
  accepted_events :: "('st, 'ev) LTS \<Rightarrow> 'st \<Rightarrow> 'ev set"
where
  "accepted_events l s \<equiv> lbl ` (outgoing l s)"

text {* 
  The inductively defined set @{term "states m"} corresponds to the set of
  reachable states of a given LTS @{text m}. 
*}

inductive_set states :: "('st, 'ev) LTS \<Rightarrow> 'st set" 
  for l :: "('st, 'ev) LTS" where
  base[elim!]: "s \<in> init l \<Longrightarrow> s \<in> states l"
| step[elim!]: "\<lbrakk>s \<in> states l; t \<in> outgoing l s\<rbrakk> \<Longrightarrow> dst t \<in> states l"

inductive_cases base : "s \<in> states l"
inductive_cases step : "dst t \<in> states l"

text {* 
  A few lemmas related to reachable states are then enunciated and proved. 
  First, all the initial states are reachable states:
*}

lemma reachable_init: "init l \<subseteq> states l"
  by auto

text {* Next, the successors states of the reachable states are themselves reachable states.
We first define a function @{text "successors"} that returns the set of successors of a
given set @{text "S"} of states in a given LTS @{text "l"}: *}

definition successors :: "('st, 'ev) LTS \<Rightarrow> 'st set \<Rightarrow> 'st set" where
  "successors l S \<equiv> dst ` (UNION S (outgoing l))"

text {* Next, we show that the successors of the reachable states are also reachable. *}

lemma reachable_stable: "successors l (states l) \<subseteq> states l"
  unfolding successors_def by auto

text {* 
  The following lemma is at the basis of proofs of invariants, and more
  generally, safety properties. Any set @{text S} that contains all initial
  states and is closed under successors contains all reachable states.
*}

lemma reachable_induct_set:
  assumes s: "s \<in> states l"
  and "init l \<subseteq> S"
  and "successors l S \<subseteq> S"
  shows "s \<in> S"
  using assms by (induct s) (auto simp: successors_def)

text {*
  The following lemma is similar but stated in terms of a predicate.
  It contains the principle for proving invariants.
*}
lemmas reachable_induct_predicate = states.induct
text {* @{thm reachable_induct_predicate} *}

text {*
  The \emph{alphabet} of an LTS is defined as the set of labels
  appearing at some reachable state.
*}

definition alphabet where
  "alphabet l \<equiv> UNION (states l) (accepted_events l)"


subsection {* Behavior *}

text {* 
  Two views of (finitary) behavior are formalized. The first view is
  the internal behavior: a \emph{run} is an initial state, followed by
  an alternating sequence of events and states that correspond to
  transitions of the LTS.

  The second, external view of behavior, abstracts from the states and
  only records the events that occur in a run.
*}

subsubsection {* Internal behaviour *}

record ('st,'ev) Run =
  trns :: "('st \<times> 'ev) list"
  fins :: "'st"

text {* 
  The inductive set @{text "runs l"} denotes the set of finite executions
  of the LTS @{text "l"}, viewed as lists of transitions. There are two base 
  cases, corresponding to the empty execution and to executions with a 
  single transition whose source state is an initial state.
*}

definition append_tr :: "('st,'ev) Run \<Rightarrow> ('st,'ev) Tr \<Rightarrow> ('st,'ev) Run" where
  "append_tr run t \<equiv> \<lparr> trns = (trns run) @ [(fins run, lbl t)], fins = dst t \<rparr>"

inductive_set runs :: "('st, 'ev) LTS \<Rightarrow> ('st, 'ev) Run set"  
  for l :: "('st, 'ev) LTS" where
  start: "s \<in> init l \<Longrightarrow> \<lparr> trns = [], fins = s \<rparr> \<in> runs l"
| step : "\<lbrakk> run \<in> runs l; t \<in> outgoing l (fins run) \<rbrakk> \<Longrightarrow> append_tr run t \<in> runs l"

text {* 
  The following lemma states that every run starts in an initial state of @{text l}.
*}
lemma run_starts_initial: 
  assumes "r \<in> runs l"
  shows "(if trns r = [] then fins r else fst (hd (trns r))) \<in> init l"
  using assms by (induct r, auto simp: append_tr_def hd_append)

text {*
  All steps in a run correspond to transitions of the LTS.
*}
lemma run_steps:
  assumes "r \<in> runs l" and "i < length (trns r)"
  shows "\<lparr> src = fst (trns r ! i), 
           dst = (if Suc i < length (trns r) then fst (trns r ! (Suc i)) else fins r),
           lbl = snd (trns r ! i) \<rparr>
         \<in> trans l"
     (is "?t r i \<in> trans l")
proof -
  {
    fix run tr
    assume run: "run \<in> runs l" and tr: "tr \<in> outgoing l (fins run)"
       and i: "i < length (trns (append_tr run tr))"
       and ih: "i < length (trns run) \<Longrightarrow> ?t run i \<in> trans l"
    have "?t (append_tr run tr) i \<in> trans l"
    proof (cases "i < length (trns run)")
      case True with ih show ?thesis
        by (auto simp: append_tr_def nth_append)
    next
      case False with i have len: "i = length (trns run)"
        by (simp add: append_tr_def)
      with tr have "?t (append_tr run tr) i = tr"
        by (simp add: append_tr_def outgoing_def nth_append)
      with tr show ?thesis
        by (simp add: outgoing_def)
    qed
  }
  with assms show ?thesis by (induct r, auto)
qed

text {*
  The set of runs is closed under prefixes.
*}
lemma prefix_is_run:
  assumes "r \<in> runs l" and "n < length (trns r) - 1"
  shows "\<lparr> trns = take n (trns r), fins = fst ((trns r)!n) \<rparr> \<in> runs l"
proof -
  {
    fix r' t n'
    assume r': "r' \<in> runs l"
       and n': "n' < length (trns r')"
       and t: "t \<in> outgoing l (fins r')"
       and ih: "\<And>m. m < length (trns r') - Suc 0 \<Longrightarrow>
                     \<lparr> trns = take m (trns r'),
                       fins = fst (trns r' ! m) \<rparr> \<in> runs l"
    have "\<lparr> trns = take n' (trns r'),
            fins = fst ((trns r' @ [(fins r', lbl t)]) ! n')\<rparr> \<in> runs l"
      (is "?run \<in> runs l")
    proof (cases "n' < length (trns r') - Suc 0")
      case True with ih n' show ?thesis
        by (simp add: nth_append)
    next
      case False
      with n' have len: "n' = length (trns r') - Suc 0" by auto
      from r' show ?thesis
      proof (cases r')
        fix s
        assume "r' = \<lparr> trns = [], fins = s \<rparr>"
        with n' show ?thesis by auto  (* r' cannot be empty *)
      next
        fix r'' t'
        assume r'': "r'' \<in> runs l"
           and t': "t' \<in> outgoing l (fins r'')"
           and r': "r' = append_tr r'' t'"
        with len have "?run = r''" by (auto simp: append_tr_def)
        with r'' show ?thesis by simp
      qed
    qed
  }
  with assms show ?thesis
    by (induct r arbitrary: n, auto simp: append_tr_def)
qed

text {*
  The reachable states are exactly the final states of runs.
*}
lemma states_runs_iff:
  "s \<in> states l \<longleftrightarrow> s \<in> fins ` (runs l)"
proof
  assume "s \<in> states l" thus "s \<in> fins ` (runs l)"
  proof (induct)
    fix s'
    assume "s' \<in> init l" thus "s' \<in> fins ` (runs l)"
      using image_iff runs.start by fastforce
  next
    fix s' t
    assume "s' \<in> fins ` (runs l)" "t \<in> outgoing l s'"
    thus "dst t \<in> fins ` (runs l)"
      by (metis (no_types, lifting) 
            Run.select_convs(2) append_tr_def image_iff runs.step)
  qed
next
  assume "s \<in> fins ` (runs l)"
  then obtain run where "run \<in> runs l" "s = fins run" by blast
  thus "s \<in> states l"
    by (induct arbitrary: s, auto simp: append_tr_def intro: states.step)
qed
  

subsubsection {* External behavior. *}

text {* 
  The external, or observable, behavior of a LTS is obtained by
  projecting the internal behavior to the events labeling its 
  transitions. We call this a \emph{trace} of the LTS.
*}

type_synonym 'ev Trace = "'ev list"

definition trace_of :: "('st, 'ev) Run \<Rightarrow> 'ev Trace" where
  "trace_of run \<equiv> map snd (trns run)"

lemma trace_of_length [simp]: 
  "length (trace_of run) = length (trns run)"
  unfolding trace_of_def by simp

definition traces :: "('st, 'ev) LTS \<Rightarrow> 'ev Trace set" where
  "traces l \<equiv> trace_of ` (runs l)"

end

