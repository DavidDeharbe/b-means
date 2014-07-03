theory LTS

imports Main

begin

section {* Execution models *}

subsection {* Labeled transition systems *}

text {* The semantics of a B component is a discrete, eventful, state-transition systems. We 
first define what is meant exactly by such systems. Any system is, at a given time in a state. 
Conversely, a system has a set of possible states. A system evolves from state to state,
and such changes called transitions. The following record definition of 
@{text "('st, 'ev) Transition}"} models transitions, where the parametric sorts @{text "'st"} 
and @{text "'ev"} represent states and events, respectively. *}

record ('st, 'ev) Tr =
  src :: 'st -- "source state"
  dst :: 'st -- "destination state"
  lbl :: 'ev -- "labeling event"

text {* Building on this formalization of transitions, the record @{text "('st, 'ev) LTS"} 
formalizes labeled transition systems (LTS):  *}

record ('st, 'ev) LTS =
  init :: "'st set" -- "set of initial states"
  trans :: "('st, 'ev) Tr set" -- "set of transitions"

text {* The inductively defined set @{term "states"} yields the reachable states of a 
given LTS. *}

inductive_set states :: "('st, 'ev) LTS \<Rightarrow> 'st set" for m :: "('st, 'ev) LTS" where
  base[elim!]: "s \<in> init m \<Longrightarrow> s \<in> states m"
| step[elim!]: "\<lbrakk> t \<in> trans m; src t \<in> states m \<rbrakk> \<Longrightarrow> dst t \<in> states m"
  
text {* A few lemmas related to reachable states are then enunciated and proved. 
First, all the initial states are reachable states:*}

lemma reachable_init: "init m \<subseteq> states m" 
  by auto

text {* Next, the successors states of the reachable states are themselves reachable states.
We first define a function @{text "successors"} that returns the set of successors of a
given set @{text "S"} of states in a given LTS @{text "L"}: *}

definition successors :: "('st, 'ev) LTS \<Rightarrow> 'st set \<Rightarrow> 'st set" where
"successors L S \<equiv> { s | s . \<exists> t \<in> trans L. src t \<in> S \<and> dst t = s}"

text {* Next, we show that the successors of the reachable states are also reachable. *}

lemma reachable_stable: "successors m (states m) \<subseteq> states m"
  unfolding successors_def by auto
  
text {* The following lemma is related to the identification of sufficient conditions to establish 
safety properties. Consider a property that is satisfied by some set of states $S$. If the initial 
states are in $S$, and if the successors of $S$ are in $S$ then all the reachable states are in 
$S$. *}

lemma reachable_induct_set:
  assumes base: "init m \<subseteq> S" and step: "successors m S \<subseteq> S"
  shows "(states m) \<subseteq> S"
proof
  fix x
  assume "x \<in> states m"
  thus "x \<in> S"
  proof (induct x)
    fix i
    assume "i \<in> init m"
    with base show "i \<in> S" ..
  next
    fix t
    assume "t \<in> trans m" "src t \<in> states m" "src t \<in> S"
    with step show "dst t \<in> S" unfolding successors_def by auto
  qed
qed

text {* Next we enunciate and prove a similar lemma for predicates. In a LTS @{text "L"}, 
if every initial state
statisfies some predicate @{text "P"} and, for each transition, whenever the source state
satisfies @{text "P"}, the destination state also satisfies @{text "P"}, then all the
reachable states satisfy @{text "P"} (and this is an invariant of the LTS). *}
lemma reachable_induct_predicate:
  assumes base: "\<forall> s \<in> init L . P s" and 
          step: "\<forall> t \<in> trans L . P (src t) \<longrightarrow> P (dst t)"
  shows "\<forall> s \<in> (states L) . P s"
proof
  fix x
  assume "x \<in> states L" 
  thus "P x"
  proof (induct x)
    fix i
    assume "i \<in> init L"
    with base show "P i" ..
  next
    fix t
    assume "t \<in> trans L" "src t \<in> states L" "P (src t)"
    with step show "P (dst t)" unfolding successors_def by auto
  qed
qed

subsection {* Behavior *}

subsubsection {* Internal behaviour *}

text {* Two views of behavior are formalized. The first view is the internal behavior, and
corresponds to the set of possible executions. An execution is a sequence of transitions, such
that two consecutive transitions have coincident state. We introduce the abbreviation @{text "Run"}
to name the type for executions: *}

type_synonym ('st, 'ev) Run = "('st, 'ev) Tr list"

text {* The inductive set @{text "runs"}
denotes all possible executions of a given LTS @{text "L"}. There are two base cases, 
corresponding to the empty execution and to executions with a single transition: *}

inductive_set runs :: "('st, 'ev) LTS \<Rightarrow> ('st, 'ev) Run set"  
          for L :: "('st, 'ev) LTS" where
  base: "[] \<in> runs L"
| start: "\<lbrakk> t \<in> trans L; src t \<in> init L \<rbrakk> \<Longrightarrow> [t] \<in> runs L"
| step: "\<lbrakk> t \<in> trans L; r \<noteq> []; r \<in> runs L; src t = dst (last r) \<rbrakk> \<Longrightarrow> r @ [t] \<in> runs L"

inductive_cases empty_run : "[] \<in> runs m"
inductive_cases one_step_run : "[t] \<in> runs m"
inductive_cases multi_step_run : "r @ [t] \<in> runs m"

lemma 
assumes "t \<in> trans L \<and> src t \<in> init L"
shows "[t] \<in> runs L"
by (metis assms runs.start)

text {* The following lemma states that for any run $r$ of a LTS $m$, such that $r$ is not the 
empty run, then the source state of the first transition is an initial state of $m$. *}

lemma "r \<in> runs m \<Longrightarrow> r \<noteq> [] \<Longrightarrow> src(hd r) \<in> init m"
proof(induct rule: runs.induct, auto)
qed

subsubsection {* External behavior. *}

text {* The external, or observable, behavior of a LTS is restricted to the events labeling its 
transitions. We give the name @{text "Trace"} to the type of event lists: *}

type_synonym 'ev Trace = "'ev list"

text {* We define the \emph{trace} of a run to be the sequence of events along that run: *}

fun "trace_of_run" :: "('st, 'ev) Run \<Rightarrow> 'ev Trace" 
where
"trace_of_run [] = []" |
"trace_of_run (t # ts) = (lbl t) # (trace_of_run ts)"

text {* We then define the \emph{traces} of an LTS from the corresponding runs: *}

definition traces :: "('st, 'ev) LTS \<Rightarrow> 'ev Trace set" where
  "traces m \<equiv> { trace_of_run r | r . r \<in> runs m }"

end

