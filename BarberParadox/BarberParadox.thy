theory BarberParadox
imports
  HOL 
begin
declare [[show_types]]

text{*
This forward proof of the barber paradox relies only on lemmas from HOL and immediate proof
steps (".").
*}
lemma barber_paradox:
fixes
  --"The barber is a man."
  barber::"'man" and
  --"Men shave men."
  shaves::"'man \<Rightarrow> 'man \<Rightarrow> bool" (infix "<shaves>" 40)
assumes
  --"The barber shaves every man who does not shave himself."
  1: "\<forall>man. barber <shaves> man \<longleftrightarrow> \<not> man <shaves> man"
shows
  False   -- "I.e. this shaving constellation cannot work."
proof -
  from spec 1
    have 2: "barber <shaves> barber \<longleftrightarrow> \<not> barber <shaves> barber" .
    --"A special instance of the assumption says that the barber shaves himself iff he doesn't..." 
  from 2
    have 3: "\<not>(barber <shaves> barber \<longleftrightarrow> barber <shaves> barber)"
    unfolding not_iff .
    --"When we drift the negation up the syntax tree, this looks even more paradoxical."
  from impE 3
    have 4: "(barber <shaves> barber \<longleftrightarrow> barber <shaves> barber) \<Longrightarrow> False"
    unfolding not_def .
    --"...Just unfolding the definition of negation and lifting it to the mata logic..."
  from 4 refl
    show "False" . 
    --"...Shows the idea that the barber shaves every man who does not shave himself
      clashes with the axiom that '\<longleftrightarrow>' is reflexive."
qed


end

