sig
  <tp : type>
  <arrow  : tp -> tp -> tp>
  <forall : (tp -> tp) -> tp>
  <tm : tp -> type>
  <lam  : (tm A -> tm B) -> tm (arrow A B)>
  <app  : tm (arrow A B) -> tm A -> tm B>
  <val : tm A -> type>
  <val_lam  : val (lam M)>
  <beta_ro : tm A -> tm A -> type>
  <bro_ctr  : beta_ro (app (lam M) N) (M N)>
  <bro_appl : beta_ro (app M N) (app M' N)
             <- beta_ro M M'>
  <bro_appr : beta_ro (app M N) (app M N')
             <- beta_ro N N'>
  <nstm : tm A -> type>
  <nstm_v  : nstm M
         <- val M>
  <nstm_nv : nstm M
            <- beta_ro M N> ;

(* That's what I would like to write
fun prog : <M:tm T> -> <nstm M>
  = fn <lam _> => <nstm_v val_lam>
     | <app M1 M2> =>
         (case (prog <M1>) of
            <nstm_nv D> => <nstm_nv bro_ctr>
          | <nstm_v val_lam> => <nstm_nv bro_ctr>) ;

*)
fun prog : <M:tm T> -> <nstm M>
  = fn <lam _> => <nstm_v val_lam>
     | <app (lam M1) M2> =>
         (case (prog <lam M1>) of
            <nstm_nv D> => <nstm_nv bro_ctr>
          | <nstm_v val_lam> => <nstm_nv bro_ctr>) ;

