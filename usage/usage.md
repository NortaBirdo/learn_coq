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
 - simpl. reflWexivity.
 - simpl. reflexivity.
Qed.
</pre>

# Бесшовность алгоритмов.

Пусть алгоритм заданный шагами `Step1`, `Step2`, `Step3` возможно представить функциями `f`, `h`, `g` соответственно, такими что:

1. Функции образуют композицию функций $g \circ h \circ f $
1. Выходной тип предшествующий функции совпадает с входным типом последующей

Тогда, в случае, если каждая из функций полностью покрывает возможности своего типа, результирующая цепочка типов будет обладать транзитивностью на всем наборе данных.

Пример на списках:

<pre>
Example trans_eq_example'' : ∀ (a b c d e f : nat),
     [a;b] = [c;d] →
     [c;d] = [e;f] →
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  transitivity [c;d].
  apply eq1. apply eq2.
Qed.

</pre>