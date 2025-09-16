# Эквивалентность двух функций

Старая
<pre>
Definition hd (default : nat) (l : natlist) : nat :=
  match l with
  | nil => default
  | h :: t => h
  end.
</pre>

Новая
<pre>
Definition hd_error (l : natlist) : natoption :=
 match l with 
 | nil => None
 | h::t => Some h
 end. 
</pre>

Теорема
<pre>
Definition option_elim (d : nat) (o : natoption) : nat :=
  match o with
  | Some n' => n'
  | None => d
  end.

Theorem option_elim_hd : forall (l:natlist) (default:nat),
  hd default l = option_elim default (hd_error l).
Proof.
 intros. induction l.
 - simpl. reflexivity.
 - simpl. reflexivity.
Qed.
</pre>