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
  inv :: "'astate \<times> 'cstate \<Rightarrow> bool"
begin
  definition sound :: bool where
    "sound \<equiv> true"
end


end
