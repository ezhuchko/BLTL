pragma Goals : printall.

require import AllCore List Int Bool Distr SmtMap DInterval.



(* MAC *)

type macKey, mac, message.

op mKeygen : macKey distr. 
op macGen : macKey -> message -> mac.
op macVer : macKey -> mac -> message -> bool. 

(* Correctness of MAC *)
axiom macCorrect : forall k m, k \in mKeygen => macVer k (macGen k m) m = true. 

(*
(* Endorsement Scheme  *)

abstract theory Endorsements.

(* Parameter types and operators *)

type pkey, skey, endorsement, end_msg.

op endKeygen : end_msg list -> (skey * pkey) distr.
op endGen : skey -> end_msg list -> int -> endorsement.
op endVer : pkey -> endorsement -> end_msg -> int -> bool.

(* Correctness of Endorsement Scheme *)

axiom endCorrect : forall pk sk i xs m, (sk, pk) \in endKeygen xs => 1 <= i <= size xs => endVer pk (endGen sk xs i) m i = true.     

end Endorsements.

clone Endorsements as E with type pkey <- pkey,
                             type skey <- skey,
                             type endorsement <- endorsement,
                             type end_msg <- end_msg,
                             op endKeygen <- endKeygen,
                             op endGen <- endGen,
                             op endVer <- endVer.
*)

(* Endorsement Oracle *) 

type pkey, skey, endorsement, end_msg.

op endKeygen : end_msg list -> (skey * pkey) distr.
op endGen : skey -> end_msg list -> int -> endorsement.
op endVer : pkey -> endorsement -> end_msg -> int -> bool.

axiom endCorrect : forall pk sk i xs m, (sk, pk) \in endKeygen xs => 1 <= i <= size xs => endVer pk (endGen sk xs i) m i = true. 

module type EndOracleT = {
  proc *init(xs : end_msg list) : skey * pkey
  proc genEnd(i : int) : endorsement 
  proc verEnd(e : endorsement, m : end_msg, i : int) : bool
}.

module EndOracle : EndOracleT = {

  var pk : pkey
  var sk : skey
  var xs : end_msg list 

  proc init(xsp : end_msg list) : skey * pkey = {
  (sk, pk) <$ endKeygen xsp;
  xs <- xsp;
  return (sk, pk);
  }

  proc genEnd(i : int) : endorsement = {
    return endGen sk xs i;
  }

  proc verEnd(e : endorsement, m : end_msg, i : int) : bool = {
    return endVer pk e m i;
  }

}. 


module EndCorrect = {
  proc main(ml : end_msg list) = {
    var e : endorsement;
    var b : bool;
    var x : int;

    x <$ [1 .. size ml];
    EndOracle.init(ml);
    e <- EndOracle.genEnd(x);
    b <- EndOracle.verEnd(e, nth witness ml x, x);
    return b;
  }
}.

print Distr.

lemma EndOracleCorrect &m ml: 
  Pr[ EndCorrect.main(ml) @ &m : res ] = 1%r.  
(* proof. byphoare => //. conseq (: _ ==> true)(:_ ==> res). progress.*)
proof. byphoare => //. proc. inline*. wp. 
seq 1 : (1 <= x <= size ml).
rnd. skip. progress. 
rnd. admit. 
rnd (fun (skpk : skey * pkey) => true). wp.
skip. progress. 
admit. admit. admit. auto.
qed.


(* Publisher *)

type Time = int.
type digest.
 
module P = {
 
  var m : (Time, digest) fmap 
  
  proc publish(t : Time, t' : Time, d : digest) : Time = {
    if (t < t'){
      t <- t'; 
      m <- m.[t <- d];
    }
      return t;
   }

  proc get(t : Time) : digest option = {
    return m.[t];
  }

}.

(*
(* Timestamping *)

abstract theory TagcommScheme.

type tag, data, cert.
type requestT = tag * data.

(* Tag-commitment scheme *)

op digestTs : requestT list -> digest.
op certTs : requestT list -> cert.
op verifyTs : digest -> cert -> requestT -> bool.

op tdistr : int distr. 

(* axiom Tscorrect : \forall rl t d, ... verifyTs (digestTs rl) (certTs rl) (t, d) = true.*)

end TagcommScheme.*)

type tag, data, cert.
type message_macced = message * mac.
type requestT = (tag * data) list.

(* Tag-commitment scheme *)

op digestTs : requestT -> digest.
op certTs : requestT -> cert list.
op verifyTs : digest -> cert -> requestT -> bool.

op tdistr : int distr. 

(* axiom Tscorrect(rl : requestT, d : digest, c : cert) : d \in digestTs rl => c \in certTs rl => verifyTs (digestTs rl) (certTs rl) (t, d) = true.*)


module Ts  = {

  var i : Time
  var t : Time
  var t' : Time

  proc init() : unit = {
    i <$ tdistr;
    t <- i;
    t' <- t + 1;
  }

  proc clock() : Time = {
    return t;
  }

  proc processQuery(ql : (tag * data) list) : Time * cert list = {
    var cs : cert list; 
    var dg : digest;
     
    dg <- digestTs ql;
    t <@ P.publish(t, t', dg);
    cs <- certTs ql;
    return (t, cs); 
  }
}.


(*
(* BLT Aggregator *)

abstract theory Accumulator.

type pkey, tag, data, Proof.
type request.

op accKey : pkey distr.
op digestQ : pkey -> request list -> data. 
op proofQ : pkey -> request list -> request -> Proof.
op verifyQ : pkey -> data -> Proof -> request -> bool.

(* rq \in ml *)
axiom accumCorrect : forall rq pk ml, pk \in accKey => verifyQ pk (digestQ pk ml) (proofQ pk ml rq) rq = true. 

end Accumulator.

clone Accumulator as A with type pkey <- pkey,
                            type tag <- tag,
                            type data <- data,
                            type Proof <- Proof,
                            type request <- tag * message,
                            op accKey <- accKey,
                            op digestQ <- digestQ,
                            op proofQ <- proofQ,
                            op verifyQ <- verifyQ.
*)

type Proof.

op accKey : pkey distr.
op digestQ : pkey -> (tag * (message_macced list)) list -> (tag * data) list. 
op proofQ : pkey -> (tag * (message_macced list)) list -> message_macced -> Proof.
op verifyQ : pkey -> (tag * data) list -> Proof -> (tag * message list) -> bool.

print List.
abbrev (\inl) ['a] (z : 'a) (s : 'a list) : bool = mem s z.

op convertQ : (tag * message_macced) list -> (tag * (message_macced list)) list.
axiom convertQ_prop1 : forall xs t m,  (t,m) \inl xs => exists (x : (tag * (message_macced list))), x \inl (convertQ xs) /\ x.`1 = t /\ m \inl x.`2.

op getByTag : tag -> (tag * (message_macced list)) list -> (message_macced list).



(* rq \in ml *)
(* axiom accumCorrect : forall (rq : tag * message list) pk (rl : (tag * data) list), pk \in accKey => rq \in rl => verifyQ pk (digestQ pk rl) (proofQ pk rl rq) rq = true. 
*)

module type AdvQ = {
  proc askForMore (t : tag, m : message_macced) : (tag * message_macced) list
}. 


module Q (A : AdvQ) = {

  var pk : pkey

  proc init() : unit = {
    pk <$ accKey;
  }

  proc processQuery(t : tag, m : message_macced) : Time * cert list * (tag * (message_macced list)) list = {
    var r, r', joined_r : (tag * message_macced) list;
    var final_r : (tag * (message_macced list)) list;
    var digested_r : (tag * data) list;
    var p : Proof; 
    var tp : Time;    (* time published *)
    var cs : cert list;
     
    r <- A.askForMore(t, m);
    (* excludes the event which might happen with negligible probability *)
    r' <- filter (fun (tm : tag * message_macced) => tm.`1 <> t) r; 
    joined_r <- r ++ [(t, m)];  
    final_r <- convertQ joined_r;
    digested_r <- digestQ pk final_r; 
    
    (* send request to Ts *)
    (tp, cs) <@ Ts.processQuery(digested_r); 

    p <- proofQ pk final_r m;
    return (tp, cs, final_r); (* (time, cert, set) back to user *)
  }
}.


(* Key gen *)
op paramDistr : int -> int -> (int list) list distr.

axiom keygen_r : forall xss i j, xss \in paramDistr i j => size xss = i /\ (forall xs, xs \in xss => size xs = j).  (* valid length of xss *)


(* BLTL Scheme *)    
module BLTLScheme(TsO : TS, EndO : EndOracleT) = {

    proc keygen(i : int, j : int) = {  
    var mac_k : mkey;
    var xss, hashed_xss : (int list) list;
   
    
    mac_k <$ mKeygen;
    xss <- paramDistr i j;  (* sk list r *)
    hashed_xss <- map(fun xs => map xs (fun x => H x)) xss; (* pk list M *)
    EndO.init(hashed_xss); 
  }
}.
