Section five_houses.

(* Definitions and axioms *)
Definition left_inv {A B:Type} (f1:A->B) (f2:B->A) : Prop :=
  forall (a:A), f2 (f1 a) = a.

Definition right_inv {A B:Type} (f1:A->B) (f2:B->A) : Prop :=
  forall (b:B), f1 (f2 b) = b.

Definition bijective {A B:Type} (f1:A->B) (f2:B->A) : Prop := 
  left_inv f1 f2 /\ right_inv f1 f2.

Inductive owner : Type :=
| a : owner
| b : owner
| c : owner
| d : owner
| e : owner.

Inductive nationality : Type :=
| dane : nationality
| brit : nationality
| swede : nationality
| norwegian : nationality
| german : nationality.

Parameter to_citizen : owner -> nationality.
Parameter from_citizen : nationality -> owner.

Axiom citizen_biject : bijective to_citizen from_citizen.

Inductive color : Type :=
| yellow : color
| red : color
| white : color
| green : color
| blue : color.

Parameter to_house : owner -> color.
Parameter from_house : color -> owner.

Axiom house_biject : bijective to_house from_house.

Inductive animal : Type :=
| horse : animal
| cat : animal
| bird : animal
| fish : animal
| dog : animal.

Parameter to_pet : owner -> animal.
Parameter from_pet : animal -> owner.

Axiom pet_biject : bijective to_pet from_pet.

Inductive beverage : Type :=
| water : beverage
| tea : beverage
| milk : beverage
| coffee : beverage
| root_beer : beverage.

Parameter to_drink : owner -> beverage.
Parameter from_drink : beverage -> owner.

Axiom drink_biject : bijective to_drink from_drink.

Inductive cigar : Type :=
| pall_mall : cigar
| prince : cigar
| blue_master : cigar
| dunhill : cigar
| blends : cigar.

Parameter to_smoke : owner -> cigar.
Parameter from_smoke : cigar -> owner.

Axiom smoke_biject : bijective to_smoke from_smoke.

Definition left_of (X1 X2 : owner) : Prop :=
  match X1, X2 with
    | a, b => True
    | b, c => True
    | c, d => True
    | d, e => True
    | _, _ => False
  end.

Definition next_to (X1 X2 : owner) : Prop :=
  left_of X1 X2 \/ left_of X2 X1.

Axiom clue1: (* The Brit lives in the house with red walls. *)
  from_citizen brit = from_house red.

Axiom clue2: (* The Swede has a dog. *)
  from_citizen swede = from_pet dog.

Axiom clue3: (* The Dane drinks tea. *)
  from_citizen dane = from_drink tea.

Axiom clue4: (* The house with green walls is directly to the left of the house with white walls. *)
  left_of (from_house green) (from_house white).

Axiom clue5: (* The owner of the house with green walls drinks coffee. *)
  from_house green = from_drink coffee.

Axiom clue6: (* The person who smokes Pall Mall cigars owns a bird. *)
  from_smoke pall_mall = from_pet bird.

Axiom clue7: (* The owner of the house with yellow walls smokes Dunhill. *)
  from_house yellow = from_smoke dunhill.

Axiom clue8: (* The man living in the center house drinks milk. *)
  to_drink c = milk.

Axiom clue9: (* The Norwegian lives in the first house. *)
  to_citizen a = norwegian.

Axiom clue10: (* The man who smokes blends lives next to the cat owner. *)
  next_to (from_smoke blends) (from_pet cat).

Axiom clue11: (* The horse’s owner lives next to the man who smokes Dunhill. *)
  next_to (from_pet horse) (from_smoke dunhill).

Axiom clue12: (* The man who smokes Blue Master drinks root beer. *)
  from_smoke blue_master = from_drink root_beer.

Axiom clue13: (* The German smokes Prince. *)
  from_citizen german = from_smoke prince.

Axiom clue14: (* The Norwegian lives next to the house with blue walls. *)
  next_to (from_citizen norwegian) (from_house blue).

Axiom clue15: (* The man who smokes Blends lives next to the man who drinks water. *)
  next_to (from_smoke blends) (from_drink water).

(* prelimilary theorems *)
(* identity for bijection *)
Theorem biject_ident : 
  forall {A B : Type}  {f1 : A-> B} {f2: B->A} (a : A) (b : B), bijective f1 f2 -> (f1 a = b <-> a = f2 b).
Proof.
  intros.
  elim H.
  intros.
  split.
  intros.
  rewrite <- H2.
  assert (f2 (f1 a0)=a0).
  apply (H0 a0).
  rewrite H3.
  reflexivity.
  intros.
  rewrite H2.
  apply (H1 b0).
Qed.

(* specification of biject_ident *)
Theorem citizen_ident:
  forall (a:owner)(b:nationality), to_citizen a = b <-> a = from_citizen b.
Proof.
  intros.
  split;intros;apply (biject_ident a0 b0 citizen_biject); assumption.
Qed.

Theorem house_ident:
  forall (a:owner)(b:color), to_house a = b <-> a = from_house b.
Proof.
  intros.
  split; intros; apply (biject_ident a0 b0 house_biject); assumption.
Qed.

Theorem pet_ident:
  forall (a:owner)(b:animal), to_pet a = b <-> a = from_pet b.
Proof.
  intros.
  split; intros; apply (biject_ident a0 b0 pet_biject); assumption.
Qed.

Theorem drink_ident:
  forall (a:owner)(b:beverage), to_drink a = b <-> a = from_drink b.
Proof.
  intros.
  split; intros; apply (biject_ident a0 b0 drink_biject); assumption.
Qed.

Theorem smoke_ident:
  forall (a:owner)(b:cigar), to_smoke a = b <-> a = from_smoke b.
Proof.
  intros.
  split; intros; apply (biject_ident a0 b0 smoke_biject); assumption.
Qed.

(* function property: a = b -> f a = f b *)
Theorem func_prop :
  forall {A B : Type} (f : A->B) (a1 a2 : A), a1 = a2 -> f a1 = f a2.
Proof.
  intros.
  rewrite H; reflexivity.
Qed.

(* left injection *)
Theorem inject_l : forall {A B : Type} {f1 : A->B}{f2:B->A}, bijective f1 f2 -> forall a1 a2:A, f1 a1 = f1 a2 -> a1 = a2.
Proof.
  intros.
  destruct H.
  assert (f2 (f1 a1) = f2 (f1 a2)).
  rewrite H0; reflexivity.
  rewrite H in H2.
  rewrite H in H2.
  assumption.
Qed.

(* right injection *)
Theorem inject_r : forall {A B : Type} {f1 : A->B}{f2:B->A}, bijective f1 f2 -> forall b1 b2:B, f2 b1 = f2 b2 -> b1 = b2.
Proof.
  intros.
  destruct H.
  assert (f1 (f2 b1) = f1 (f2 b2)).
  rewrite H0; reflexivity.
  rewrite H1 in H2.
  rewrite H1 in H2.
  assumption.
Qed.

(* left surjection *)
Theorem surject_l : forall {A B:Type}{f1 : A->B}{f2:B->A}, bijective f1 f2 -> forall b : B, exists a : A, f1 a = b.
Proof.
  intros.
  destruct H.
  assert ( f1 (f2 b0) = b0 ).
  apply H0.
  exists (f2 b0).
  assumption.
Qed.

(* right surjection *)
Theorem surject_r : forall {A B:Type}{f1 : A->B}{f2:B->A}, bijective f1 f2 -> forall a : A, exists b : B, f2 b = a.
Proof.
  intros.
  destruct H.
  assert ( f2 (f1 a0) = a0 ).
  apply H.
  exists (f1 a0).
  assumption.
Qed.

(* lemma for left_of and next to *)
Lemma a_left_of_b : forall X:owner, left_of a X -> X = b.
Proof.
  intros.
  induction X; simpl in H; contradiction || reflexivity.
Qed.

Lemma d_left_of_e : forall X:owner, left_of d X -> X = e.
Proof.
  intros.
  induction X; simpl in H; contradiction || reflexivity.
Qed.

Lemma e_left_of_no : forall X:owner, left_of e X -> False.
Proof.
  intros.
  induction X; simpl in H; contradiction.
Qed.

Lemma b_next_to_a : forall X:owner, next_to a X -> X = b.
Proof.
  intros.
  destruct H.
  apply a_left_of_b; assumption.
  induction X; simpl in H; contradiction.
Qed.

Lemma b_next_to_a' : forall X:owner, next_to X a -> X = b.
Proof.
  intros.
  destruct H.
  induction X; simpl in H; contradiction.
  apply a_left_of_b; assumption.
Qed.

Lemma blue_is_b : to_house b = blue.
Proof.
  assert (a = from_citizen norwegian).
  apply citizen_ident.
  exact clue9.
  apply house_ident.
  apply eq_sym.
  apply b_next_to_a.
  rewrite H.
  exact clue14.
Qed.

Lemma green_is_d : to_house d = green.
Proof.
  assert (to_house a <> green).
  intro H.
  apply house_ident in H.
  generalize clue4; intros.
  rewrite <- H in H0.
  apply a_left_of_b in H0.
  apply eq_sym in H0.
  apply house_ident in H0.
  rewrite blue_is_b in H0; discriminate.
  assert (to_house b <> green).
  intro.
  rewrite blue_is_b in H0; discriminate.
  assert (to_house c <> green).
  intro.
  apply house_ident in H1.
  rewrite clue5 in H1.
  apply drink_ident in H1.
  rewrite clue8 in H1; discriminate.
  assert (to_house e <> green).
  intro.
  apply house_ident in H2.
  generalize clue4; intros.
  rewrite <- H2 in H3.
  apply (e_left_of_no (from_house white)); assumption.
  assert (exists x:owner, to_house x = green).
  apply (surject_l house_biject).
  elim H3; intros.
  induction x; contradiction || assumption.
Qed.

Lemma white_is_e : to_house e = white.
Proof.
  generalize clue4 green_is_d; intros.
  apply house_ident in H0.
  rewrite <- H0 in H.
  apply d_left_of_e in H.
  apply eq_sym in H.
  apply house_ident in H.
  assumption.
Qed.

Lemma red_is_c : to_house c = red.
Proof.
  assert (to_house a <> red).
  intro H.
  apply house_ident in H.
  rewrite <- clue1 in H.
  apply citizen_ident in H.
  rewrite clue9 in H; discriminate.
  assert (to_house b <> red).
  intro H0; rewrite blue_is_b in H0; discriminate.
  assert (to_house d <> red).
  intro H1; rewrite green_is_d in H1; discriminate.
  assert (to_house e <> red).
  intro H2; rewrite white_is_e in H2; discriminate.
  assert (exists x:owner, to_house x = red).
  apply (surject_l house_biject).
  elim H3; intros.
  induction x; contradiction || assumption.
Qed.

Lemma yellow_is_a : to_house a = yellow.
Proof.
  assert (to_house b <> yellow).
  intro H; rewrite blue_is_b in H; discriminate.
  assert (to_house c <> yellow).
  intro H0; rewrite red_is_c in H0; discriminate.
  assert (to_house d <> yellow).
  intro H1; rewrite green_is_d in H1; discriminate.
  assert (to_house e <> yellow).
  intro H2; rewrite white_is_e in H2; discriminate.
  assert (exists x:owner, to_house x = yellow).
  apply (surject_l house_biject).
  elim H3; intros.
  induction x; contradiction || assumption.
Qed.

Lemma c_is_brit : to_citizen c = brit.
Proof.
  apply citizen_ident.
  rewrite clue1.
  apply house_ident.
  apply red_is_c.
Qed.

Lemma a_smoke_dunhill : to_smoke a = dunhill.
Proof.
  apply smoke_ident.
  rewrite <- clue7.
  apply house_ident.
  apply yellow_is_a.
Qed.

Lemma d_drink_coffee : to_drink d = coffee.
Proof.
  apply drink_ident.
  rewrite <- clue5.
  apply house_ident.
  apply green_is_d.
Qed.

Lemma b_have_horse : to_pet b = horse.
Proof.
  generalize clue11 a_smoke_dunhill; intros.
  apply smoke_ident in H0.
  rewrite <- H0 in H.
  apply b_next_to_a' in H.
  apply pet_ident.
  apply eq_sym.
  assumption.
Qed.

Lemma citizen_b_not_swede : to_citizen b <> swede.
Proof.
  intro.
  apply citizen_ident in H.
  rewrite clue2 in H.
  apply pet_ident in H.
  rewrite b_have_horse in H.
  discriminate.
Qed.

Lemma dane_not_e : to_citizen e <> dane.
Proof.
  intro.
  generalize H.
  apply citizen_ident in H.
  rewrite clue3 in H.
  apply drink_ident in H.
  assert (to_drink e <> root_beer).
  intro.
  rewrite H in H0; discriminate.
  assert (to_drink c <> root_beer).
  intro H1; rewrite clue8 in H1; discriminate.
  assert (to_drink d <> root_beer).
  intro H2; rewrite d_drink_coffee in H2; discriminate.
  assert (to_drink a <> root_beer).
  intro.
  apply drink_ident in H3.
  rewrite <- clue12 in H3.
  apply smoke_ident in H3.
  rewrite a_smoke_dunhill in H3; discriminate.
  assert (exists x:owner, to_drink x = root_beer).
  apply (surject_l drink_biject).
  elim H4; intros.
  induction x; try contradiction.
  apply drink_ident in H5.
  rewrite <- clue12 in H5.
  assert (to_citizen e <> swede).
  intro Hn0; rewrite H6 in Hn0; discriminate.
  assert (to_citizen a <> swede).
  intro Hn1; rewrite clue9 in Hn1; discriminate.
  assert (to_citizen c <> swede).
  intro Hn2; rewrite c_is_brit in Hn2; discriminate.
  generalize citizen_b_not_swede; intro.
  assert (exists x:owner, to_citizen x = swede).
  apply (surject_l citizen_biject).
  elim H11; intros.
  induction x; try contradiction.
  assert (to_citizen e <> german).
  intro Hn0; rewrite H6 in Hn0; discriminate.
  assert (to_citizen a <> german).
  intro Hn1; rewrite clue9 in Hn1; discriminate.
  assert (to_citizen c <> german).
  intro Hn2; rewrite c_is_brit in Hn2; discriminate.
  assert (to_citizen d <> german).
  intro Hn3; rewrite H12 in Hn3; discriminate.
  assert (exists x:owner, to_citizen x = german).
  apply (surject_l citizen_biject).
  elim H17; intros.
  induction x; try contradiction.
  apply citizen_ident in H18.
  rewrite clue13 in H18.
  rewrite H5 in H18.
  apply (inject_r smoke_biject) in H18; discriminate.
Qed.

Lemma b_is_dane : to_citizen b = dane.
Proof.
  assert (to_citizen a <> dane).
  intro Hn0; rewrite clue9 in Hn0; discriminate.
  assert (to_citizen c <> dane).
  intros Hn1; rewrite c_is_brit in Hn1; discriminate.
  assert (to_citizen d <> dane).
  intro Hn2.
  apply citizen_ident in Hn2.
  rewrite clue3 in Hn2.
  apply drink_ident in Hn2.
  rewrite d_drink_coffee in Hn2; discriminate.
  generalize dane_not_e; intros.
  assert (exists x:owner, to_citizen x = dane).
  apply (surject_l citizen_biject).
  elim H3;intros.
  induction x; contradiction || assumption.
Qed.

Lemma b_drink_tea : to_drink b = tea.
Proof.
  apply drink_ident.
  rewrite <- clue3.
  apply citizen_ident.
  exact b_is_dane.
Qed.

Lemma e_drink_root_beer : to_drink e = root_beer.
Proof.
  assert (to_drink a <> root_beer).
  intro.
  apply drink_ident in H.
  rewrite <- clue12 in H.
  apply smoke_ident in H.
  rewrite a_smoke_dunhill in H; discriminate.
  assert (to_drink b <> root_beer).
  intro Hn0; rewrite b_drink_tea in Hn0; discriminate.
  assert (to_drink c <> root_beer).
  intro Hn0; rewrite clue8 in Hn0; discriminate.
  assert (to_drink d <> root_beer).
  intro Hn0; rewrite d_drink_coffee in Hn0; discriminate.
  assert (exists x:owner, to_drink x = root_beer).
  apply (surject_l drink_biject).
  elim H3; intros.
  induction x; contradiction || assumption.
Qed.

Lemma e_smoke_blue_master : to_smoke e = blue_master.
Proof.
  apply smoke_ident.
  rewrite clue12.
  apply drink_ident.
  exact e_drink_root_beer.
Qed.

Lemma a_drink_water : to_drink a = water.
Proof.
  assert (to_drink b <> water).
  intro Hn; rewrite b_drink_tea in Hn; discriminate.
  assert (to_drink c <> water).
  intro Hn; rewrite clue8 in Hn; discriminate.
  assert (to_drink d <> water).
  intro Hn; rewrite d_drink_coffee in Hn; discriminate.
  assert (to_drink e <> water).
  intro Hn; rewrite e_drink_root_beer in Hn; discriminate.
  assert (exists x:owner, to_drink x = water).
  apply (surject_l drink_biject).
  elim H3; intros.
  induction x; contradiction || assumption.
Qed.

Lemma b_smoke_blends : to_smoke b = blends.
Proof.
  generalize clue15, a_drink_water; intros.
  apply drink_ident in H0.
  rewrite <- H0 in H.
  apply b_next_to_a' in H.
  apply smoke_ident.
  rewrite H; reflexivity.
Qed.

Lemma d_smoke_prince : to_smoke d = prince.
Proof.
  assert (to_smoke a <> prince).
  intro Hn; rewrite a_smoke_dunhill in Hn; discriminate.
  assert (to_smoke b <> prince).
  intro Hn; rewrite b_smoke_blends in Hn; discriminate.
  assert (to_smoke e <> prince).
  intro Hn; rewrite e_smoke_blue_master in Hn; discriminate.
  assert (to_smoke c <> prince).
  intro Hn.
  apply smoke_ident in Hn.
  rewrite <- clue13 in Hn.
  apply citizen_ident in Hn.
  rewrite c_is_brit in Hn; discriminate.
  assert (exists x:owner, to_smoke x = prince).
  apply (surject_l smoke_biject).
  elim H3; intros.
  induction x; contradiction || assumption.
Qed.

Lemma c_smoke_pall_mall : to_smoke c = pall_mall.
Proof.
  assert (to_smoke a <> pall_mall).
  intro Hn; rewrite a_smoke_dunhill in Hn; discriminate.
  assert (to_smoke b <> pall_mall).
  intro Hn; rewrite b_smoke_blends in Hn; discriminate.
  assert (to_smoke d <> pall_mall).
  intro Hn; rewrite d_smoke_prince in Hn; discriminate.
  assert (to_smoke e <> pall_mall).
  intro Hn; rewrite e_smoke_blue_master in Hn; discriminate.
  assert (exists x:owner, to_smoke x = pall_mall).
  apply (surject_l smoke_biject).
  elim H3; intros.
  induction x; contradiction || assumption.
Qed.

Lemma c_have_bird : to_pet c = bird.
Proof.
  apply pet_ident.
  rewrite <- clue6.
  apply smoke_ident.
  exact c_smoke_pall_mall.
Qed.

Lemma d_is_german : to_citizen d = german.
Proof.
  apply citizen_ident.
  rewrite clue13.
  apply smoke_ident.
  exact d_smoke_prince.
Qed.

Lemma e_is_swede : to_citizen e = swede.
Proof.
  assert (to_citizen a <> swede).
  intro Hn; rewrite clue9 in Hn; discriminate.
  assert (to_citizen b <> swede).
  intro Hn; rewrite b_is_dane in Hn; discriminate.
  assert (to_citizen c <> swede).
  intro Hn; rewrite c_is_brit in Hn; discriminate.
  assert (to_citizen d <> swede).
  intro Hn; rewrite d_is_german in Hn; discriminate.
  assert (exists x:owner, to_citizen x = swede).
  apply (surject_l citizen_biject).
  elim H3; intros.
  induction x; contradiction || assumption.
Qed.

Lemma e_have_dog : to_pet e = dog.
Proof.
  apply pet_ident.
  rewrite <- clue2.
  apply citizen_ident.
  exact e_is_swede.
Qed.

Lemma a_have_cat : to_pet a = cat.
Proof.
  assert (to_pet b <> cat).
  intro Hn; rewrite b_have_horse in Hn; discriminate.
  assert (to_pet c <> cat).
  intro Hn; rewrite c_have_bird in Hn; discriminate.
  assert (to_pet e <> cat).
  intro Hn; rewrite e_have_dog in Hn; discriminate.
  assert (to_pet d <> cat).
  intro Hn.
  apply pet_ident in Hn.
  generalize clue10, b_smoke_blends; intros.
  rewrite <- Hn in H2.
  apply smoke_ident in H3.
  rewrite <- H3 in H2.
  destruct H2; simpl in H2; assumption.
  assert (exists x:owner, to_pet x = cat).
  apply (surject_l pet_biject).
  elim H3; intros.
  induction x; contradiction || assumption.
Qed.

Theorem d_have_fish : to_pet d = fish.
Proof.
  assert (to_pet a <> fish).
  intro Hn; rewrite a_have_cat in Hn; discriminate.
  assert (to_pet b <> fish).
  intro Hn; rewrite b_have_horse in Hn; discriminate.
  assert (to_pet c <> fish).
  intro Hn; rewrite c_have_bird in Hn; discriminate.
  assert (to_pet e <> fish).
  intro Hn; rewrite e_have_dog in Hn; discriminate.
  assert (exists x:owner, to_pet x = fish).
  apply (surject_l pet_biject).
  elim H3; intros.
  induction x; contradiction || assumption.
Qed.

End five_houses.