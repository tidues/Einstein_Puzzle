Section five_houses.

(* Definitions and axioms *)

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

Parameter citizen : owner -> nationality.

Inductive color : Type :=
| yellow : color
| red : color
| white : color
| green : color
| blue : color.

Parameter house : owner -> color.

Inductive animal : Type :=
| horse : animal
| cat : animal
| bird : animal
| fish : animal
| dog : animal.

Parameter pet : owner -> animal.

Inductive beverage : Type :=
| water : beverage
| tea : beverage
| milk : beverage
| coffee : beverage
| root_beer : beverage.

Parameter drink : owner -> beverage.

Inductive cigar : Type :=
| pall_mall : cigar
| prince : cigar
| blue_master : cigar
| dunhill : cigar
| blends : cigar.

Parameter smoke : owner -> cigar.

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

Definition surjective {A B:Type}(f: A->B) : Prop :=
  forall b:B, exists a : A, f a = b.

Definition injective {A B:Type}(f: A-> B) :Prop :=
  forall a1 a2:A, f a1 = f a2 -> a1 = a2.

Definition bijective {A B:Type}(f: A-> B) :Prop :=
  surjective f /\ injective f.

Axiom citizen_is_bijective : bijective citizen.
Axiom house_is_bijective : bijective house.
Axiom pet_is_bijective : bijective pet.
Axiom drink_is_bijective : bijective drink.
Axiom smoke_is_bijective : bijective smoke.

Axiom clue1: (* The Brit lives in the house with red walls. *)
  forall X : owner,  house X = red -> citizen X = brit.

Axiom clue2: (* The Swede has a dog. *)
  forall X : owner, citizen X = swede -> pet X = dog.

Axiom clue3: (* The Dane drinks tea. *)
  forall X : owner, citizen X = dane -> drink X = tea.

Axiom clue4: (* The house with green walls is directly to the left of the house with white walls. *)
  forall X1 X2 : owner,
    house X1 = green -> (left_of X1 X2 <-> house X2 = white).

Axiom clue5: (* The owner of the house with green walls drinks coffee. *)
  forall X : owner, house X = green -> drink X = coffee.

Axiom clue6: (* The person who smokes Pall Mall cigars owns a bird. *)
  forall X : owner, smoke X = pall_mall -> pet X = bird.

Axiom clue7: (* The owner of the house with yellow walls smokes Dunhill. *)
  forall X : owner, house X = yellow -> smoke X = dunhill.

Axiom clue8: (* The man living in the center house drinks milk. *)
  drink c = milk.

Axiom clue9: (* The Norwegian lives in the first house. *)
  citizen a = norwegian.

Axiom clue10: (* The man who smokes blends lives next to the cat owner. *)
  forall X1 X2 : owner,
    smoke X1 = blends -> pet X2 = cat -> next_to X1 X2.

Axiom clue11: (* The horse’s owner lives next to the man who smokes Dunhill. *)
  forall X1 X2: owner,
    pet X1 = horse -> smoke X2 = dunhill -> next_to X1 X2.

Axiom clue12: (* The man who smokes Blue Master drinks root beer. *)
  forall X : owner, drink X = root_beer -> smoke X = blue_master.

Axiom clue13: (* The German smokes Prince. *)
  forall X : owner, citizen X = german -> smoke X = prince.

Axiom clue14: (* The Norwegian lives next to the house with blue walls. *)
  forall X1 X2 : owner,
    citizen X1 = norwegian -> house X2 = blue -> next_to X1 X2.

Axiom clue15: (* The man who smokes Blends lives next to the man who drinks water. *)
  forall X1 X2 : owner,
    smoke X1 = blends -> drink X2 = water -> next_to X1 X2.

Lemma b_next_to_a : forall X:owner, next_to a X-> X = b.
Proof.
  intros.
  case H.
  case X; simpl; intros; try discriminate; contradiction || reflexivity.
  case X; simpl; contradiction || reflexivity.
Qed.

Lemma next_to_comm : forall a b:owner, next_to a b -> next_to b a.
Proof.
  intros.
  destruct H.
  right; assumption.
  left; assumption.
Qed.

Lemma b_next_to_a' : forall X:owner, next_to X a -> X = b.
Proof.
  intros.
  assert (next_to a X).
  apply (next_to_comm X a); assumption.
  apply b_next_to_a; assumption.
Qed.

Lemma clue14_0 :
  forall X1 X2 : owner,
    citizen X1 = norwegian -> house X2 = blue -> next_to a X2.
Proof.
  intros.
  apply clue14.
  exact clue9.
  assumption.
Qed.

Lemma clue14_1 :
  forall X1 X2 : owner,
    citizen X1 = norwegian -> house X2 = blue -> X2 = b.
Proof.
  intros.
  apply b_next_to_a.
  eapply clue14_0.
  exact clue9.
  assumption.
Qed.

Lemma clue14_2 :
  forall X1 X2 : owner,
    citizen X1 = norwegian -> house X2 = blue -> house b = blue.
Proof.
  intros.
  erewrite <- clue14_1.
  exact H0.
  exact clue9.
  assumption.
Qed.

Lemma b_color_blue : house b = blue.
Proof.
  assert (citizen a = norwegian).
  exact clue9.
  assert (exists X3:owner, house X3 = blue).
  generalize house_is_bijective.
  intros.
  destruct H0.
  apply H0.
  elim H0.
  intros.
  apply (clue14_2 a x).
  exact H.
  exact H1.
Qed.

Lemma green_is_d : house d = green.
Proof.
  assert ( house c <> green ).
  intros H.
  generalize clue8, clue5.
  intros.
  assert ( drink c = coffee ).
  apply H1.
  assumption.
  rewrite H0 in H2.
  discriminate.
  assert ( house b <> green).
  generalize b_color_blue;intros.
  intros H1.
  rewrite H0 in H1.
  discriminate.
  assert ( house a <> green ).
  intros H1.
  assert (house b = white ).
  apply (clue4 a b).
  assumption.
  simpl; exact I.
  generalize b_color_blue; intros.
  rewrite H2 in H3.
  discriminate.
  assert ( house e <> green ).
  intro H2.
  assert (exists x:owner, left_of e x).
  assert ( exists x:owner, house x = white).
  generalize house_is_bijective; intros.
  destruct H3.
  apply (H3 white).
  elim H3; intros.
  assert (left_of e x).
  apply (clue4 e x); assumption.
  exists x; assumption.
  elim H3; intros.
  simpl in H4; assumption.
  assert (exists x:owner, house x = green).
  generalize house_is_bijective; intros.
  destruct H3.
  apply H3.
  generalize H3.
  elim H3.
  intros.
  induction x; contradiction || assumption.
Qed.

Lemma white_is_e : house e = white.
Proof.
  apply (clue4 d e).
  apply green_is_d.
  simpl.
  exact I.
Qed.

Lemma red_is_c : house c = red.
Proof.
  assert (house a <> red).
  intros H.
  assert (citizen a = brit).
  apply clue1; assumption.
  generalize clue9; intros.
  rewrite H0 in H1; discriminate.
  assert (exists a : owner, house a = red).
  generalize house_is_bijective; intro Hhb; destruct Hhb.
  apply H0.
  elim H0; intros.
  induction x.
  contradiction.
  generalize b_color_blue;intros.
  rewrite H1 in H2; discriminate.
  assumption.
  generalize green_is_d; intros.
  rewrite H1 in H2; discriminate.
  generalize white_is_e; intros.
  rewrite H1 in H2; discriminate.
Qed.

Lemma yellow_is_a : house a = yellow.
Proof.
  generalize b_color_blue red_is_c green_is_d white_is_e; intros H0 H1 H2 H3.
  assert (exists a : owner, house a = yellow).
  generalize house_is_bijective; intro Hhb; destruct Hhb.
  apply H.
  elim H; intros.
  induction x; try assumption.
  rewrite H0 in H4; discriminate.
  rewrite H1 in H4; discriminate.
  rewrite H2 in H4; discriminate.
  rewrite H3 in H4; discriminate.
Qed.

Lemma c_is_brit : citizen c = brit.
Proof.
  apply (clue1 c).
  apply red_is_c.
Qed.

Lemma a_smoke_dunhill : smoke a = dunhill.
Proof.
  apply (clue7 a).
  apply yellow_is_a.
Qed.

Lemma d_drink_coffee : drink d = coffee.
Proof.
  apply (clue5 d).
  apply green_is_d.
Qed.

Lemma b_have_horse : pet b = horse.
Proof.
  assert (forall X:owner, next_to X a -> X = b).
  intros.
  case H; induction X; simpl; intros; contradiction || reflexivity.
  assert (forall X:owner, pet X = horse -> smoke a = dunhill -> pet b = horse ).
  intros.
  replace b with X.
  assumption.
  apply H.
  apply clue11; assumption.
  assert (exists x: owner, pet x = horse).
  generalize pet_is_bijective;intro Hpb; destruct Hpb.
  apply H1.
  elim H1; intros.
  apply (H0 x).
  assumption.
  apply a_smoke_dunhill.
Qed.

Lemma citizen_b_not_swede : citizen b <> swede.
Proof.
  intro H.
  assert (pet b = dog).
  apply (clue2 b); assumption.
  generalize b_have_horse; intros.
  rewrite H0 in H1.
  discriminate.
Qed.

Lemma dane_not_e : citizen e <> dane.
Proof.
  intro H.
  assert (citizen d = swede).
  generalize citizen_b_not_swede; intros.
  assert (citizen e <> swede).
  intros H1.
  rewrite H in H1; discriminate.
  assert (citizen a <> swede).
  generalize clue9; intros.
  intro H3.
  rewrite H2 in H3; discriminate.
  assert (citizen c <> swede).
  generalize c_is_brit; intros.
  intro H4.
  rewrite H3 in H4; discriminate.
  assert (exists x:owner, citizen x = swede).
  generalize citizen_is_bijective; intros Hcb; destruct Hcb.
  apply H4.
  elim H4; intros.
  induction x; try contradiction || assumption.
  assert (citizen b = german).
  generalize clue9 c_is_brit; intros.
  assert (exists x:owner, citizen x = german).
  generalize citizen_is_bijective; intros Hcb; destruct Hcb.
  apply H3.
  elim H3; intros.
  induction x.
  rewrite H1 in H4; discriminate.
  assumption.
  rewrite H2 in H4; discriminate.
  rewrite H0 in H4; discriminate.
  rewrite H in H4; discriminate.
  assert (smoke b = prince).
  apply (clue13 b); assumption.
  assert (drink e = tea).
  apply (clue3 e); assumption.
  generalize clue8 d_drink_coffee; intros.
  assert (drink a <> root_beer).
  intro H6.
  assert (smoke a = blue_master).
  apply (clue12 a); assumption.
  generalize a_smoke_dunhill; intros.
  rewrite H7 in H8; discriminate.
  assert (drink b = root_beer).
  assert (exists x:owner, drink x = root_beer).
  generalize drink_is_bijective; intro Hdb; destruct Hdb.
  apply H7.
  elim H7; intros.
  induction x.
  contradiction.
  assumption.
  rewrite H4 in H8; discriminate.
  rewrite H5 in H8; discriminate.
  rewrite H3 in H8; discriminate.
  assert (smoke b = blue_master).
  apply (clue12 b); assumption.
  rewrite H2 in H8; discriminate.
Qed.

Lemma b_is_dane : citizen b = dane.
Proof.
  generalize dane_not_e; intros.
  generalize c_is_brit clue9; intros.
  assert (citizen d <> dane).
  intro H2.
  assert (drink d = tea).
  apply (clue3 d); assumption.
  generalize d_drink_coffee; intros.
  rewrite H3 in H4; discriminate.
  assert (citizen a <> dane).
  intro Hf; rewrite H1 in Hf; discriminate.
  assert (citizen c <> dane).
  intro Hf; rewrite H0 in Hf; discriminate.
  assert (exists x:owner, citizen x = dane).
  generalize citizen_is_bijective; intro Hcb; destruct Hcb.
  apply H5.
  elim H5; intros.
  induction x; contradiction || assumption.
Qed.

Lemma b_drink_tea : drink b = tea.
Proof.
  apply (clue3 b).
  exact b_is_dane.
Qed.

Lemma e_drink_root_beer : drink e = root_beer.
Proof.
  generalize clue8 b_drink_tea d_drink_coffee; intros.
  assert (drink c <> root_beer).
  rewrite H; discriminate.
  assert (drink b <> root_beer).
  rewrite H0; discriminate.
  assert (drink d <> root_beer).
  rewrite H1; discriminate.
  assert (drink a <> root_beer).
  intros Hf.
  cut (smoke a = blue_master).
  intros.
  generalize a_smoke_dunhill; intros.
  rewrite H5 in H6; discriminate.
  apply (clue12 a); assumption.
  assert (exists x:owner, drink x = root_beer).
  generalize drink_is_bijective; intro Hdb; destruct Hdb.
  apply H6.
  elim H6; intros.
  induction x; contradiction || assumption.
Qed.

Lemma e_smoke_blue_master : smoke e = blue_master.
Proof.
  apply (clue12 e).
  exact e_drink_root_beer.
Qed.

Lemma a_drink_water : drink a = water.
Proof.
  assert (drink b <> water).
  generalize b_drink_tea; intro Hs; rewrite Hs; discriminate.
  assert (drink c <> water).
  generalize clue8; intro Hs; rewrite Hs; discriminate.
  assert (drink d <> water).
  generalize d_drink_coffee; intro Hs; rewrite Hs; discriminate.
  assert (drink e <> water).
  generalize e_drink_root_beer; intro Hs; rewrite Hs; discriminate.
  assert (exists x:owner, drink x = water).
  generalize drink_is_bijective; intro Hdb; destruct Hdb.
  apply H3.
  elim H3; intros.
  induction x; contradiction || assumption.
Qed.

Lemma b_smoke_blends : smoke b = blends.
Proof.
  assert (forall X: owner, smoke X = blends -> drink a = water -> smoke b = blends); intros.
  rewrite <- H.
  assert (X = b).
  apply (b_next_to_a' X).
  apply clue15.
  assumption.
  assumption.
  rewrite H1; reflexivity.
  assert (exists x:owner, smoke x = blends).
  generalize smoke_is_bijective; intro Hsb; destruct Hsb.
  apply H0.
  elim H0; intros.
  apply (H x).
  assumption.
  exact a_drink_water.
Qed.

Lemma d_smoke_prince : smoke d = prince.
Proof.
  assert (smoke a <> prince).
  generalize a_smoke_dunhill; intros Hs; rewrite Hs; discriminate.
  assert (smoke b <> prince).
  generalize b_smoke_blends; intros Hs; rewrite Hs; discriminate.
  assert (smoke e <> prince).
  generalize e_smoke_blue_master; intros Hs; rewrite Hs; discriminate.
  assert (smoke c <> prince).
  intro Hf.
  assert (forall X : owner, citizen X = german -> citizen c = german).
  intros.
  assert (X = c).
  generalize smoke_is_bijective; intros Hsb; destruct Hsb.
  apply H4.
  rewrite Hf.
  apply clue13; assumption.
  assert(exists x:owner, citizen x = german).
  generalize citizen_is_bijective; intros Hcb; destruct Hcb.
  apply H4.
  rewrite <- H2.
  rewrite H3; reflexivity.
  assert(exists x:owner, citizen x = german).
  generalize citizen_is_bijective; intros Hcb; destruct Hcb.
  apply H3.
  elim H3; intros.
  assert (citizen c = german).
  apply (H2 x); assumption.
  generalize c_is_brit; intros.
  rewrite H5 in H6; discriminate.
  assert (exists x:owner, smoke x = prince).
  generalize smoke_is_bijective; intros Hsb; destruct Hsb.
  apply H3.
  elim H3; intros.
  induction x; contradiction || assumption.
Qed.

Lemma c_smoke_pall_mall : smoke c = pall_mall.
  assert (smoke a <> pall_mall).
  generalize a_smoke_dunhill; intros Hs; rewrite Hs; discriminate.
  assert (smoke b <> pall_mall).
  generalize b_smoke_blends; intros Hs; rewrite Hs; discriminate.
  assert (smoke d <> pall_mall).
  generalize d_smoke_prince; intros Hs; rewrite Hs; discriminate.
  assert (smoke e <> pall_mall).
  generalize e_smoke_blue_master; intros Hs; rewrite Hs; discriminate.
  assert (exists x:owner, smoke x = pall_mall).
  generalize smoke_is_bijective; intro Hsb; destruct Hsb.
  apply H3.
  elim H3; intros.
  induction x; contradiction || assumption.
Qed.

Lemma c_have_bird : pet c = bird.
Proof.
  apply (clue6 c).
  apply c_smoke_pall_mall.
Qed.

Lemma d_is_german : citizen d = german.
Proof.
  assert (forall X : owner, citizen X = german -> citizen d = german).
  intros.
  cut (X = d); intros.
  rewrite <- H0; assumption.
  generalize (clue13 X); intros.
  assert (smoke X = prince).
  apply H0; assumption.
  generalize d_smoke_prince; intros.
  rewrite <- H1 in H2.
  generalize smoke_is_bijective; intro Hsb; destruct Hsb.
  apply H4; rewrite H2; reflexivity.
  assert (exists x:owner, citizen x = german).
  generalize citizen_is_bijective; intro Csb; destruct Csb.
  apply H0.
  elim H0; intros.
  apply (H x); assumption.
Qed.

Lemma e_is_swede : citizen e = swede.
Proof.
  assert (citizen a <> swede).
  generalize clue9; intros Hs; rewrite Hs; discriminate.
  assert (citizen b <> swede).
  generalize b_is_dane; intros Hs; rewrite Hs; discriminate.
  assert (citizen c <> swede).
  generalize c_is_brit; intros Hs; rewrite Hs; discriminate.
  assert (citizen d <> swede).
  generalize d_is_german; intros Hs; rewrite Hs; discriminate.
  assert (exists x:owner, citizen x = swede).
  generalize citizen_is_bijective; intro Hcb; destruct Hcb.
  apply H3.
  elim H3; intros.
  induction x; contradiction || assumption.
Qed.

Lemma e_have_dog : pet e = dog.
Proof.
  apply (clue2 e).
  apply e_is_swede.
Qed.

Lemma a_have_cat : pet a = cat.
Proof.
  assert (pet d <> cat).
  intro H.
  assert (next_to b d).
  apply (clue10 b d).
  apply b_smoke_blends.
  assumption.
  destruct H0.
  simpl in H0; assumption.
  simpl in H0; assumption.
  assert (pet b <> cat).
  generalize b_have_horse; intros Hs; rewrite Hs; discriminate.
  assert (pet c <> cat).
  generalize c_have_bird; intros Hs; rewrite Hs; discriminate.
  assert (pet e <> cat).
  generalize e_have_dog; intros Hs; rewrite Hs; discriminate.
  assert (exists x: owner, pet x = cat).
  generalize pet_is_bijective; intro Hcb; destruct Hcb.
  apply H3.
  elim H3; intros.
  induction x; contradiction || assumption.
Qed.

Theorem d_have_fish : pet d = fish.
Proof.
  assert (pet a <> fish).
  generalize a_have_cat; intros Hs; rewrite Hs; discriminate.
  assert (pet b <> fish).
  generalize b_have_horse; intros Hs; rewrite Hs; discriminate.
  assert (pet c <> fish).
  generalize c_have_bird; intros Hs; rewrite Hs; discriminate.
  assert (pet e <> fish).
  generalize e_have_dog; intros Hs; rewrite Hs; discriminate.
  assert (exists x: owner, pet x = fish).
  generalize pet_is_bijective; intro Hcb; destruct Hcb.
  apply H3.
  elim H3; intros.
  induction x; contradiction || assumption.
Qed.

Print d_have_fish.

End five_houses.
