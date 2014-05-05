theory Traces

imports Main Misc Machine

begin

section {* Behaviour: a set of traces *}

text {* Two notions of behaviours for a machine are defined: internal behaviour and observable 
behaviour. Internal behaviour is a set of paths, where each path is a pair that is composed of an
initial state, and a possibly infinite list of consecutive transitions. The type $PATH$ corresponds
to paths: *}

type_synonym PATH = "STATE \<times> TRANSITION list"

text {* Then, the function $paths$ yields the internal behaviour of a machine: *}

definition paths :: "LTS \<Rightarrow> PATH set" where
"paths m \<equiv> lfp (\<lambda> S . { (s, []) | s . s \<in> Init m } \<union> 
                        { (s, trl @ [t]) | s trl t . s \<in> Init m \<and> t \<in> Trans m \<and> 
                          (\<exists> tr \<in> S . trl = snd tr) \<and>
                          (trl = [] \<and> Src t = s \<or> trl \<noteq> [] \<and> Src t = Dst (last trl)) })"

lemma mono_paths: "mono((\<lambda> S . { (s, []) | s . s \<in> Init m } \<union> 
                               { (s, tl @ [t]) | s tl t . s \<in> Init m \<and> t \<in> Trans m \<and> 
                                    (\<exists> y \<in> S . y = snd tr) \<and>
                                    (tl = [] \<and> Src t = s \<or> tl \<noteq> [] \<and> Src t = Dst (last tl)) }))"
proof(rule monoI, blast)
qed

text {* External behaviour of a machine is the set of possible sequences of events. Each such
sequence corresponds to the events occurring along a path, as is defined for function $path\_events$: *}

definition path_events :: "PATH \<Rightarrow> EVENT list" where
"path_events p = map Evt (snd p)"

text {* External behaviour is given by the function $traces$: *}

definition traces :: "LTS \<Rightarrow> EVENT list set" where
"traces m \<equiv> { path_events p | p . p \<in> paths m } "

end
