(*意味の領域*)
Class value := {
  supp : Set;
  eq : supp -> supp -> Prop;
  eq_ref : forall (v1 :supp) , eq v1 v1;
  eq_sym : forall (v1 v2 :supp), eq v1 v2 -> eq v2 v1;
  eq_trs : forall (v1 v2 v3 :supp), eq v1 v2 /\ eq v2 v3 -> eq v1 v3;
}.

Class map (V1 :value)(V2 :value):= {
  supp_map : @supp V1 -> @supp V2;
  preserve : forall (v1 v2 : @supp V1),
    @eq V1 v1 v2 -> @eq V2 (supp_map v1) (supp_map v2);
}.

(*抽象機械と意味論*)
Class machine := {
  state : Set;
  step : state -> option state;
  stop_or : state -> bool;
  stop_means : forall m:state,
    (stop_or m = true) -> (step m = Some m) \/ (step m = None);
}.

Inductive is_halt {M :machine} : state -> Prop :=
| stop_is_halt : forall (S :state), stop_or S = true -> is_halt S
| step_by_step : forall (S S' :state), step S = Some S' /\ is_halt S' -> is_halt S.

Class machine_semantic (M :machine)(V :value) := {
  mchine_halt := is_halt;
  mchine_has_value : forall (S :state), mchine_halt S -> supp -> Prop;
  machine_partiality : forall (S :state)(l :mchine_halt S)(v1 v2 :supp),
    mchine_has_value S l v1 /\ mchine_has_value S l v2 -> eq v1 v2;
}.

(*言語と意味論*)
Class language := {
  code : Set
}.

Class language_semantic (C :language) (V :value) := {
  code_halt : code -> supp -> Prop;
  code_has_value : forall (c :code) (v :supp) , code_halt c v -> supp -> Prop;
  code_partiality :
    forall (c :code) (v :supp) (H :code_halt c v),
    forall (v1 v2 :supp),
      code_has_value c v H v1 /\ code_has_value c v H v2 -> eq v1 v2
}.

(*言語の操作的意味論*)
Class language_compile (L :language)(M :machine)(V :value) := {
  compile : code -> supp -> state;
}.

Instance operational_semantics (L :language)(V :value)
(M :machine)(U :machine_semantic M V)(C :language_compile L M V)
: language_semantic L V := {
  code_halt :=
    (fun (c :code)(v :supp) => mchn_halt (compile c v));
  code_has_value :=
    (fun (c :code)(v :supp) => mchn_has_value (compile c v) );
  code_partiality (c :code)(v :supp)(H :mchn_halt (compile c v)) :=
    (fun (v1 v2:supp) => machine_partiality (compile c v) H v1 v2);
}.



