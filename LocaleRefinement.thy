theory LocaleRefinement

imports Main LocaleLTS LocaleSimulation

begin

locale Refinement =
  abstract: LTS la
+ concrete: LTS lc
for
  la :: "('astate, 'event) LTS" and
  lc :: "('cstate, 'event) LTS"
+ 
fixes 
  inv :: "'astate \<Rightarrow> 'cstate \<Rightarrow> bool"
assumes
  po_init: "\<forall>cs \<in> init lc. \<exists>as \<in> init la. inv as cs" and
  po_step: "\<forall>as cs. inv as cs \<longrightarrow> (\<forall>ct \<in> trans lc. src ct = cs \<longrightarrow>
                (\<exists>at \<in> trans la. src at = as \<and> lbl at = lbl ct \<and> inv (dst at) (dst ct)))"
begin
end


end
