{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
module Eval where

import Data.List
import Data.Maybe (fromMaybe)
import Data.Map (Map,(!),mapWithKey,assocs,filterWithKey
                ,elems,intersectionWith,intersection,keys
                ,member,notMember,empty)
import qualified Data.Map as Map
import qualified Data.Set as Set

import Connections
import CTT

-----------------------------------------------------------------------
-- Lookup functions

look :: String -> Env -> Val
look x (Env (Upd y rho,v:vs,fs,os)) | x == y = v
                                    | otherwise = look x (Env (rho,vs,fs,os))
look x r@(Env (Def _ decls rho,vs,fs,Nameless os)) = case lookup x decls of
  Just (_,t) -> eval r t
  Nothing    -> look x (Env (rho,vs,fs,Nameless os))
look x (Env (Sub _ rho,vs,_:fs,os)) = look x (Env (rho,vs,fs,os))
look x (Env (Empty,_,_,_)) = error $ "look: not found " ++ show x

lookType :: String -> Env -> Val
lookType x (Env (Upd y rho,v:vs,fs,os))
  | x /= y        = lookType x (Env (rho,vs,fs,os))
  | VVar _ a <- v = a
  | otherwise     = error ""
lookType x r@(Env (Def _ decls rho,vs,fs,os)) = case lookup x decls of
  Just (a,_) -> eval r a
  Nothing -> lookType x (Env (rho,vs,fs,os))
lookType x (Env (Sub _ rho,vs,_:fs,os)) = lookType x (Env (rho,vs,fs,os))
lookType x (Env (Empty,_,_,_))          = error $ "lookType: not found " ++ show x

lookName :: Name -> Env -> Formula
lookName i (Env (Upd _ rho,v:vs,fs,os)) = lookName i (Env (rho,vs,fs,os))
lookName i (Env (Def _ _ rho,vs,fs,os)) = lookName i (Env (rho,vs,fs,os))
lookName i (Env (Sub j rho,vs,phi:fs,os)) | i == j    = phi
                                          | otherwise = lookName i (Env (rho,vs,fs,os))
lookName i _ = error $ "lookName: not found " ++ show i


-----------------------------------------------------------------------
-- Nominal instances

instance Nominal Ctxt where
  support _ = []
  act e _   = e
  swap e _  = e

instance Nominal Env where
  support (Env (rho,vs,fs,os)) = support (rho,vs,fs,os)
  act (Env (rho,vs,fs,os)) iphi = Env $ act (rho,vs,fs,os) iphi
  swap (Env (rho,vs,fs,os)) ij = Env $ swap (rho,vs,fs,os) ij

instance Nominal Val where
  support v = case v of
    VU                      -> []
    Ter _ e                 -> support e
    VPi u v                 -> support [u,v]
    -- VComp a u ts            -> support (a,u,ts)
    VPathP a v0 v1          -> support [a,v0,v1]
    VPLam i v               -> i `delete` support v
    VSigma u v              -> support (u,v)
    VPair u v               -> support (u,v)
    VFst u                  -> support u
    VSnd u                  -> support u
    VCon _ vs               -> support vs
    VPCon _ a vs phis       -> support (a,vs,phis)
    VHComp a u ts           -> support (a,u,ts)
    VTrans a phi u          -> support (a,phi,u)
    VVar _ v                -> support v
    VOpaque _ v             -> support v
    VApp u v                -> support (u,v)
    VLam _ u v              -> support (u,v)
    VAppFormula u phi       -> support (u,phi)
    VSplit u v              -> support (u,v)
    VGlue a ts              -> support (a,ts)
    VGlueElem a ts          -> support (a,ts)
    VUnGlueElem a ts        -> support (a,ts)
    -- VCompU a ts             -> support (a,ts)
    -- VUnGlueElemU a b es     -> support (a,b,es)
    VIdPair u us            -> support (u,us)
    VId a u v               -> support (a,u,v)
    VIdJ a u c d x p        -> support [a,u,c,d,x,p]

  act u (i, phi) | i `notElem` support u = u
                 | otherwise =
    let acti :: Nominal a => a -> a
        acti u = act u (i, phi)
        sphi = support phi
    in case u of
         VU           -> VU
         Ter t e      -> Ter t (acti e)
         VPi a f      -> VPi (acti a) (acti f)
         -- VComp a v ts -> compLine (acti a) (acti v) (acti ts)
         VPathP a u v -> VPathP (acti a) (acti u) (acti v)
         VPLam j v | j == i -> u
                   | j `notElem` sphi -> VPLam j (acti v)
                   | otherwise -> VPLam k (acti (v `swap` (j,k)))
              where k = fresh (v,Atom i,phi)
         VSigma a f              -> VSigma (acti a) (acti f)
         VPair u v               -> VPair (acti u) (acti v)
         VFst u                  -> fstVal (acti u)
         VSnd u                  -> sndVal (acti u)
         VCon c vs               -> VCon c (acti vs)
         VPCon c a vs phis       -> pcon c (acti a) (acti vs) (acti phis)
         VHComp a u us           -> hCompLine (acti a) (acti u) (acti us)
         VTrans a phi u          -> transLine (acti a) (acti phi) (acti u)
         VVar x v                -> VVar x (acti v)
         VOpaque x v             -> VOpaque x (acti v)
         VAppFormula u psi       -> acti u @@ acti psi
         VApp u v                -> app (acti u) (acti v)
         VLam x t u              -> VLam x (acti t) (acti u)
         VSplit u v              -> app (acti u) (acti v)
         VGlue a ts              -> glue (acti a) (acti ts)
         VGlueElem a ts          -> glueElem (acti a) (acti ts)
         VUnGlueElem a ts        -> unglueElem (acti a) (acti ts)
         -- VUnGlueElemU a b es     -> unGlueU (acti a) (acti b) (acti es)
         -- VCompU a ts             -> compUniv (acti a) (acti ts)
         VIdPair u us            -> VIdPair (acti u) (acti us)
         VId a u v               -> VId (acti a) (acti u) (acti v)
         VIdJ a u c d x p        ->
           idJ (acti a) (acti u) (acti c) (acti d) (acti x) (acti p)

  -- This increases efficiency as it won't trigger computation.
  swap u ij@(i,j) =
    let sw :: Nominal a => a -> a
        sw u = swap u ij
    in case u of
         VU                      -> VU
         Ter t e                 -> Ter t (sw e)
         VPi a f                 -> VPi (sw a) (sw f)
         -- VComp a v ts            -> VComp (sw a) (sw v) (sw ts)
         VPathP a u v            -> VPathP (sw a) (sw u) (sw v)
         VPLam k v               -> VPLam (swapName k ij) (sw v)
         VSigma a f              -> VSigma (sw a) (sw f)
         VPair u v               -> VPair (sw u) (sw v)
         VFst u                  -> VFst (sw u)
         VSnd u                  -> VSnd (sw u)
         VCon c vs               -> VCon c (sw vs)
         VPCon c a vs phis       -> VPCon c (sw a) (sw vs) (sw phis)
         VHComp a u us           -> VHComp (sw a) (sw u) (sw us)
         VTrans a phi u          -> VTrans (sw a) (sw phi) (sw u)
         VVar x v                -> VVar x (sw v)
         VOpaque x v             -> VOpaque x (sw v)
         VAppFormula u psi       -> VAppFormula (sw u) (sw psi)
         VApp u v                -> VApp (sw u) (sw v)
         VLam x u v              -> VLam x (sw u) (sw v)
         VSplit u v              -> VSplit (sw u) (sw v)
         VGlue a ts              -> VGlue (sw a) (sw ts)
         VGlueElem a ts          -> VGlueElem (sw a) (sw ts)
         VUnGlueElem a ts        -> VUnGlueElem (sw a) (sw ts)
         -- VUnGlueElemU a b es     -> VUnGlueElemU (sw a) (sw b) (sw es)
         -- VCompU a ts             -> VCompU (sw a) (sw ts)
         VIdPair u us            -> VIdPair (sw u) (sw us)
         VId a u v               -> VId (sw a) (sw u) (sw v)
         VIdJ a u c d x p        ->
           VIdJ (sw a) (sw u) (sw c) (sw d) (sw x) (sw p)

-----------------------------------------------------------------------
-- The evaluator

eval :: Env -> Ter -> Val
eval rho@(Env (_,_,_,Nameless os)) v = case v of
  U                   -> VU
  App r s             -> app (eval rho r) (eval rho s)
  Var i
    | i `Set.member` os -> VOpaque i (lookType i rho)
    | otherwise       -> look i rho
  Pi t@(Lam _ a _)    -> VPi (eval rho a) (eval rho t)
  Sigma t@(Lam _ a _) -> VSigma (eval rho a) (eval rho t)
  Pair a b            -> VPair (eval rho a) (eval rho b)
  Fst a               -> fstVal (eval rho a)
  Snd a               -> sndVal (eval rho a)
  Where t decls       -> eval (defWhere decls rho) t
  Con name ts         -> VCon name (map (eval rho) ts)
  PCon name a ts phis ->
    pcon name (eval rho a) (map (eval rho) ts) (map (evalFormula rho) phis)
  Lam{}               -> Ter v rho
  Split{}             -> Ter v rho
  Sum{}               -> Ter v rho
  HSum{}              -> Ter v rho
  Undef{}             -> Ter v rho
  Hole{}              -> Ter v rho
  PathP a e0 e1       -> VPathP (eval rho a) (eval rho e0) (eval rho e1)
  PLam i t            -> let j = fresh rho
                         in VPLam j (eval (sub (i,Atom j) rho) t)
  AppFormula e phi    -> eval rho e @@ evalFormula rho phi
  HComp a t0 ts       ->
    hCompLine (eval rho a) (eval rho t0) (evalSystem rho ts)
  -- HFill a t0 ts       ->
  --   hFillLine (eval rho a) (eval rho t0) (evalSystem rho ts)
  Trans a phi t       ->
    transLine (eval rho a) (evalFormula rho phi) (eval rho t)
  Comp a t0 ts        ->
    compLine (eval rho a) (eval rho t0) (evalSystem rho ts)
  Fill a t0 ts        ->
    fillLine (eval rho a) (eval rho t0) (evalSystem rho ts)
  Glue a ts           -> glue (eval rho a) (evalSystem rho ts)
  GlueElem a ts       -> glueElem (eval rho a) (evalSystem rho ts)
  UnGlueElem a ts     -> unglueElem (eval rho a) (evalSystem rho ts)
  Id a r s            -> VId (eval rho a) (eval rho r) (eval rho s)
  IdPair b ts         -> VIdPair (eval rho b) (evalSystem rho ts)
  IdJ a t c d x p     -> idJ (eval rho a) (eval rho t) (eval rho c)
                             (eval rho d) (eval rho x) (eval rho p)
  _                   -> error $ "Cannot evaluate " ++ show v

evals :: Env -> [(Ident,Ter)] -> [(Ident,Val)]
evals env bts = [ (b,eval env t) | (b,t) <- bts ]

evalFormula :: Env -> Formula -> Formula
evalFormula rho phi = case phi of
  Atom i         -> lookName i rho
  NegAtom i      -> negFormula (lookName i rho)
  phi1 :/\: phi2 -> evalFormula rho phi1 `andFormula` evalFormula rho phi2
  phi1 :\/: phi2 -> evalFormula rho phi1 `orFormula` evalFormula rho phi2
  _              -> phi

evalSystem :: Env -> System Ter -> System Val
evalSystem rho ts =
  let out = concat [ let betas = meetss [ invFormula (lookName i rho) d
                                        | (i,d) <- assocs alpha ]
                     in [ (beta,eval (rho `face` beta) talpha) | beta <- betas ]
                   | (alpha,talpha) <- assocs ts ]
  in mkSystem out

app :: Val -> Val -> Val
app u v = case (u,v) of
  (Ter (Lam x _ t) e,_) -> eval (upd (x,v) e) t
  (Ter (Split _ _ _ nvs) e,VCon c vs) -> case lookupBranch c nvs of
    Just (OBranch _ xs t) -> eval (upds (zip xs vs) e) t
    _     -> error $ "app: missing case in split for " ++ c
  (Ter (Split _ _ _ nvs) e,VPCon c _ us phis) -> case lookupBranch c nvs of
    Just (PBranch _ xs is t) -> eval (subs (zip is phis) (upds (zip xs us) e)) t
    _ -> error $ "app: missing case in split for " ++ c
  (Ter (Split _ _ ty hbr) e,VHComp a w ws) -> case eval e ty of
    VPi _ f -> let j   = fresh (e,v)
                   wsj = Map.map (@@ j) ws
                   w'  = app u w
                   ws' = mapWithKey (\alpha -> app (u `face` alpha)) wsj
                   -- a should be constant
               in comp j (app f (fill j a w wsj)) w' ws'
    _ -> error $ "app: Split annotation not a Pi type " ++ show u
  (Ter Split{} _,_) | isNeutral v -> VSplit u v
  (VTrans (VPLam i (VPi a f)) phi u0, v) ->
    let j = fresh (u,v)
        (aij,fij) = (a,f) `swap` (i,j)
        w = transFillNeg j aij phi v
        w0 = transNeg j aij phi v
    in trans j (app fij w) phi (app u0 w0)
  (VHComp (VPi a f) u0 us, v) ->
    let i = fresh (u,v)
    in hComp i (app f v) (app u0 v)
         (intersectionWith (app . (@@ i)) us (border v us))
  _ | isNeutral u       -> VApp u v
  _                     -> error $ "app \n  " ++ show u ++ "\n  " ++ show v

fstVal, sndVal :: Val -> Val
fstVal (VPair a b)     = a
fstVal u | isNeutral u = VFst u
fstVal u               = error $ "fstVal: " ++ show u ++ " is not neutral."
sndVal (VPair a b)     = b
sndVal u | isNeutral u = VSnd u
sndVal u               = error $ "sndVal: " ++ show u ++ " is not neutral."

-- infer the type of a neutral value
inferType :: Val -> Val
inferType v = case v of
  VVar _ t -> t
  VOpaque _ t -> t
  Ter (Undef _ t) rho -> eval rho t
  VFst t -> case inferType t of
    VSigma a _ -> a
    ty         -> error $ "inferType: expected Sigma type for " ++ show v
                  ++ ", got " ++ show ty
  VSnd t -> case inferType t of
    VSigma _ f -> app f (VFst t)
    ty         -> error $ "inferType: expected Sigma type for " ++ show v
                  ++ ", got " ++ show ty
  VSplit s@(Ter (Split _ _ t _) rho) v1 -> case eval rho t of
    VPi _ f -> app f v1
    ty      -> error $ "inferType: Pi type expected for split annotation in "
               ++ show v ++ ", got " ++ show ty
  VApp t0 t1 -> case inferType t0 of
    VPi _ f -> app f t1
    ty      -> error $ "inferType: expected Pi type for " ++ show v
               ++ ", got " ++ show ty
  VAppFormula t phi -> case inferType t of
    VPathP a _ _ -> a @@ phi
    ty         -> error $ "inferType: expected PathP type for " ++ show v
                  ++ ", got " ++ show ty
  VHComp a _ _ -> a
  VTrans a _ _ -> a @@ One
--  VUnGlueElem _ b _  -> b   -- This is wrong! Store the type??
  -- VUnGlueElemU _ b _ -> b
  VIdJ _ _ c _ x p -> app (app c x) p
  _ -> error $ "inferType: not neutral " ++ show v

(@@) :: ToFormula a => Val -> a -> Val
(VPLam i u) @@ phi         = u `act` (i,toFormula phi)
v@(Ter Hole{} _) @@ phi    = VAppFormula v (toFormula phi)
v @@ phi | isNeutral v     = case (inferType v,toFormula phi) of
  (VPathP _ a0 _,Dir 0) -> a0
  (VPathP _ _ a1,Dir 1) -> a1
  _                    -> VAppFormula v (toFormula phi)
v @@ phi                   = error $ "(@@): " ++ show v ++ " should be neutral."

-- Applying a *fresh* name.
(@@@) :: Val -> Name -> Val
(VPLam i u) @@@ j = u `swap` (i,j)
v @@@ j           = VAppFormula v (toFormula j)


-------------------------------------------------------------------------------
-- Composition and filling

hCompLine :: Val -> Val -> System Val -> Val
hCompLine a u us = hComp i a u (Map.map (@@ i) us)
  where i = fresh (a,u,us)

hFill :: Name -> Val -> Val -> System Val -> Val
hFill i a u us = hFill j a u (insertSystem (i ~> 0) u $ us `conj` (i,j))
  where j = fresh (Atom i,a,u,us)

hComp :: Name -> Val -> Val -> System Val -> Val
hComp i a u us | eps `member` us = (us ! eps) `face` (i ~> 1)
hComp i a u us = case a of
  VPathP p v0 v1 -> let j = fresh (Atom i,a,u,us) in
    VPLam j $ hComp i a (u @@ j) (insertsSystem [(j ~> 0,v0),(j ~> 1,v1)]
                                   (Map.map (@@ j) us))
  VId b v0 v1 -> undefined
  VSigma a f -> VPair u1comp (comp i (app f u1fill) u2 us2)
    where (us1, us2) = (Map.map fstVal us, Map.map sndVal us)
          (u1, u2) = (fstVal u, sndVal u)
          u1fill = hFill i a u1 us1
          u1comp = hComp i a u1 us1
  VU -> undefined -- hCompu
  VGlue b equivs | not (isNeutralGlueHComp equivs u us) ->
    let wts = mapWithKey
                (\al wal ->
                   app wal (hFill i (equivDom wal) (u `face` al) (us `face` al)))
                equivs
        t1s = mapWithKey (\al wal ->
                hComp i (equivDom wal) (u `face` al) (us `face` al)) equivs
        v = unGlue u b equivs
        vs = mapWithKey (\al ual -> unGlue ual (b `face` al) (equivs `face` al))
               us
        v1 = hComp i b v (vs `unionSystem` wts)
    in glueElem v1 t1s
  Ter (Sum _ _ nass) env | VCon n vs <- u, all isCon (elems us) ->
    case lookupLabel n nass of
      Just as -> let usvs = transposeSystemAndList (Map.map unCon us) vs
                     -- TODO: it is not really much of an improvement
                     -- to use hComps here; directly use comps?
                 in VCon n $ hComps i as env usvs
      Nothing -> error $ "hComp: missing constructor in sum " ++ n
  Ter (HSum _ _ _) _ -> VHComp a u (Map.map (VPLam i) us)
  VPi{} -> VHComp a u (Map.map (VPLam i) us)
  _ -> VHComp a u (Map.map (VPLam i) us)

-- TODO: has to use comps after the second component anyway... remove?
hComps :: Name -> [(Ident,Ter)] -> Env -> [(System Val,Val)] -> [Val]
hComps i []         _ []            = []
hComps i ((x,a):as) e ((ts,u):tsus) =
  let v   = hFill i (eval e a) u ts
      vi1 = hComp i (eval e a) u ts
      vs  = comps i as (upd (x,v) e) tsus -- NB: not hComps
  in vi1 : vs
hComps _ _ _ _ = error "hComps: different lengths of types and values"


-- For i:II |- a, phi # i, u : a (i/phi) we get fwd i a phi u : a(i/1)
-- such that fwd i a 1 u = u.   Note that i gets bound.
fwd :: Name -> Val -> Formula -> Val -> Val
fwd i a phi u = trans i (a `act` (i,phi :\/: Atom i)) phi u

comp :: Name -> Val -> Val -> System Val -> Val
comp i a u us = hComp i (a `face` (i ~> 1)) (fwd i a (Dir Zero) u) fwdius
  where fwdius = mapWithKey (\al ual -> fwd i (a `face` al) (Atom i) ual) us

-- comp :: Name -> Val -> Val -> System Val -> Val
-- comp i a u ts | eps `member` ts = (ts ! eps) `face` (i ~> 1)
-- comp i a u ts = case a of
--   VPathP p v0 v1 -> let j = fresh (Atom i,a,u,ts)
--                     in VPLam j $ comp i (p @@ j) (u @@ j) $
--                          insertsSystem [(j ~> 0,v0),(j ~> 1,v1)] (Map.map (@@ j) ts)
--   VId b v0 v1 -> case u of
--     VIdPair r _ | all isIdPair (elems ts) ->
--       let j = fresh (Atom i,a,u,ts)
--           VIdPair z _ @@@ phi = z @@ phi
--           sys (VIdPair _ ws)  = ws
--           w = VPLam j $ comp i b (r @@ j) $
--                           insertsSystem [(j ~> 0,v0),(j ~> 1,v1)]
--                             (Map.map (@@@ j) ts)
--       in VIdPair w (joinSystem (Map.map sys (ts `face` (i ~> 1))))
--     _ -> VComp (VPLam i a) u (Map.map (VPLam i) ts)
--   VSigma a f -> VPair ui1 comp_u2
--     where (t1s, t2s) = (Map.map fstVal ts, Map.map sndVal ts)
--           (u1,  u2)  = (fstVal u, sndVal u)
--           fill_u1    = fill i a u1 t1s
--           ui1        = comp i a u1 t1s
--           comp_u2    = comp i (app f fill_u1) u2 t2s
--   VPi{} -> VComp (VPLam i a) u (Map.map (VPLam i) ts)
--   VU -> compUniv u (Map.map (VPLam i) ts)
--   -- VCompU a es | not (isNeutralU i es u ts)  -> compU i a es u ts
--   VGlue b equivs | not (isNeutralGlue i equivs u ts) -> compGlue i b equivs u ts
--   Ter (Sum _ _ nass) env -> case u of
--     VCon n us | all isCon (elems ts) -> case lookupLabel n nass of
--       Just as -> let tsus = transposeSystemAndList (Map.map unCon ts) us
--                  in VCon n $ comps i as env tsus
--       Nothing -> error $ "comp: missing constructor in labelled sum " ++ n
--     _ -> VComp (VPLam i a) u (Map.map (VPLam i) ts)
--   Ter (HSum _ _ nass) env -> compHIT i a u ts
--   _ -> VComp (VPLam i a) u (Map.map (VPLam i) ts)

compNeg :: Name -> Val -> Val -> System Val -> Val
compNeg i a u ts = comp i (a `sym` i) u (ts `sym` i)

compLine :: Val -> Val -> System Val -> Val
compLine a u ts = comp i (a @@ i) u (Map.map (@@ i) ts)
  where i = fresh (a,u,ts)


-- TODO: this simply becomes hcomp
-- compConstLine :: Val -> Val -> System Val -> Val
-- compConstLine a u ts = comp i a u (Map.map (@@ i) ts)
--   where i = fresh (a,u,ts)

comps :: Name -> [(Ident,Ter)] -> Env -> [(System Val,Val)] -> [Val]
comps i []         _ []         = []
comps i ((x,a):as) e ((ts,u):tsus) =
  let v   = fill i (eval e a) u ts
      vi1 = comp i (eval e a) u ts
      vs  = comps i as (upd (x,v) e) tsus
  in vi1 : vs
comps _ _ _ _ = error "comps: different lengths of types and values"

fill :: Name -> Val -> Val -> System Val -> Val
fill i a u ts =
  comp j (a `conj` (i,j)) u (insertSystem (i ~> 0) u (ts `conj` (i,j)))
  where j = fresh (Atom i,a,u,ts)

fillNeg :: Name -> Val -> Val -> System Val -> Val
fillNeg i a u ts = (fill i (a `sym` i) u (ts `sym` i)) `sym` i

fillLine :: Val -> Val -> System Val -> Val
fillLine a u ts = VPLam i $ fill i (a @@ i) u (Map.map (@@ i) ts)
  where i = fresh (a,u,ts)

-- fills :: Name -> [(Ident,Ter)] -> Env -> [(System Val,Val)] -> [Val]
-- fills i []         _ []         = []
-- fills i ((x,a):as) e ((ts,u):tsus) =
--   let v  = fill i (eval e a) ts u
--       vs = fills i as (Upd e (x,v)) tsus
--   in v : vs
-- fills _ _ _ _ = error "fills: different lengths of types and values"


-----------------------------------------------------------
-- Transport and forward

transLine :: Val -> Formula -> Val -> Val
transLine a phi u = trans i (a @@ i) phi u
  where i = fresh (a,phi,u)

-- For i:II |- a, phi
--     i:II, phi=1 |- a = a(i/0)
-- and u : a(i/0) gives trans i a phi u : a(i/1) such that
-- trans i a 1 u = u : a(i/1) (= a(i/0)).
trans :: Name -> Val -> Formula -> Val -> Val
trans i a (Dir One) u = u
trans i a phi u = case a of
  VPathP p v0 v1 -> let j = fresh (Atom i,a,phi,u) in
    VPLam j $ comp i (p @@ j) (u @@ j) (mkSystem [(j ~> 0,v0),(j ~> 1,v1)])
  VId b v0 v1 -> undefined
  VSigma a f -> VPair (trans i a phi u1) (trans i (app f u1f) phi u2)
    where (u1,u2) = (fstVal u, sndVal u)
          u1f     = transFill i a phi u1
  VPi{} -> VTrans (VPLam i a) phi u
  VU -> undefined -- TODO: can we take u?
  VGlue b equivs | not (eps `notMember` equivs && isNeutral u) ->
    transGlue i b equivs phi u
  Ter (Sum _ _ nass) env -> case u of
    VCon n us -> case lookupLabel n nass of
      Just as -> VCon n (transps i as env phi us)
      Nothing -> error $ "trans: missing constructor in sum " ++ n
    _ -> VTrans (VPLam i a) phi u
  Ter (HSum _ _ nass) env -> case u of
    VCon n us -> case lookupLabel n nass of
      Just as -> VCon n (transps i as env phi us)
      Nothing -> error $ "trans: missing constructor in hsum " ++ n
    VPCon n _ us psis -> case lookupPLabel n nass of
      Just (as,is,es) -> -- TODO: do correction as for pushouts
        VPCon n (a `face` (i ~> 1)) (transps i as env phi us) psis
      Nothing -> error $ "trans: missing path constructor in hsum " ++ n
    -- TODO: double check
    VHComp _ v vs -> hCompLine (a `face` (i ~> 1)) (trans i a phi v) $
                       mapWithKey (\al val ->
                           trans i (a `face` al) (phi `face` al) val) vs
  _ -> VTrans (VPLam i a) phi u


transFill :: Name -> Val -> Formula -> Val -> Val
transFill i a phi u = trans j (a `conj` (i,j)) (phi :\/: NegAtom i) u
  where j = fresh (Atom i,a,phi,u)

transNeg :: Name -> Val -> Formula -> Val -> Val
transNeg i a phi u = trans i (a `sym` i) phi u

transFillNeg :: Name -> Val -> Formula -> Val -> Val
transFillNeg i a phi u = (transFill i (a `sym` i) phi u) `sym` i

transps :: Name -> [(Ident,Ter)] -> Env -> Formula -> [Val] -> [Val]
transps i []         _ phi []     = []
transps i ((x,a):as) e phi (u:us) =
  let v   = transFill i (eval e a) phi u
      vi1 = trans i (eval e a) phi u
      vs  = transps i as (upd (x,v) e) phi us
  in vi1 : vs
transps _ _ _ _ _ = error "transps: different lengths of types and values"


-- trans :: Name -> Val -> Val -> Val
-- trans i v0 v1 = comp i v0 v1 empty

-- transNeg :: Name -> Val -> Val -> Val
-- transNeg i a u = trans i (a `sym` i) u

-- transLine :: Val -> Val -> Val
-- transLine u v = trans i (u @@ i) v
--   where i = fresh (u,v)

-- transNegLine :: Val -> Val -> Val
-- transNegLine u v = transNeg i (u @@ i) v
--   where i = fresh (u,v)

-- -- TODO: define in terms of comps?
-- transps :: Name -> [(Ident,Ter)] -> Env -> [Val] -> [Val]
-- transps i []         _ []     = []
-- transps i ((x,a):as) e (u:us) =
--   let v   = transFill i (eval e a) u
--       vi1 = trans i (eval e a) u
--       vs  = transps i as (upd (x,v) e) us
--   in vi1 : vs
-- transps _ _ _ _ = error "transps: different lengths of types and values"

-- transFill :: Name -> Val -> Val -> Val
-- transFill i a u = fill i a u empty

-- transFillNeg :: Name -> Val -> Val -> Val
-- transFillNeg i a u = (transFill i (a `sym` i) u) `sym` i

-- -- Given u of type a "squeeze i a u" connects in the direction i
-- -- trans i a u(i=0) to u(i=1)
-- squeeze :: Name -> Val -> Val -> Val
-- squeeze i a u = comp j (a `disj` (i,j)) u $ mkSystem [ (i ~> 1, ui1) ]
--   where j   = fresh (Atom i,a,u)
--         ui1 = u `face` (i ~> 1)

-- squeezes :: Name -> [(Ident,Ter)] -> Env -> [Val] -> [Val]
-- squeezes i xas e us = comps j xas (e `disj` (i,j)) us'
--   where j   = fresh (us,e,Atom i)
--         us' = [ (mkSystem [(i ~> 1, u `face` (i ~> 1))],u) | u <- us ]


-------------------------------------------------------------------------------
-- | Id

idJ :: Val -> Val -> Val -> Val -> Val -> Val -> Val
idJ a v c d x p = case p of
  VIdPair w ws -> comp i (app (app c (w @@ i)) w') d
                    (border d (shape ws))
    where w' = VIdPair (VPLam j $ w @@ (Atom i :/\: Atom j))
                  (insertSystem (i ~> 0) v ws)
          i:j:_ = freshs [a,v,c,d,x,p]
  _ -> VIdJ a v c d x p

isIdPair :: Val -> Bool
isIdPair VIdPair{} = True
isIdPair _         = False


-------------------------------------------------------------------------------
-- | HITs

pcon :: LIdent -> Val -> [Val] -> [Formula] -> Val
pcon c a@(Ter (HSum _ _ lbls) rho) us phis = case lookupPLabel c lbls of
  Just (tele,is,ts) | eps `member` vs -> vs ! eps
                    | otherwise       -> VPCon c a us phis
    where rho' = subs (zip is phis) (updsTele tele us rho)
          vs   = evalSystem rho' ts
  Nothing           -> error "pcon"
pcon c a us phi     = VPCon c a us phi

-- compHIT :: Name -> Val -> Val -> System Val -> Val
-- compHIT i a u us
--   | isNeutral u || isNeutralSystem us =
--       VComp (VPLam i a) u (Map.map (VPLam i) us)
--   | otherwise =
--       hComp (a `face` (i ~> 1)) (transpHIT i a u) $
--         mapWithKey (\alpha uAlpha ->
--                      VPLam i $ squeezeHIT i (a `face` alpha) uAlpha) us

-- -- Given u of type a(i=0), transpHIT i a u is an element of a(i=1).
-- transpHIT :: Name -> Val -> Val -> Val
-- transpHIT i a@(Ter (HSum _ _ nass) env) u =
--  let j = fresh (a,u)
--      aij = swap a (i,j)
--  in
--  case u of
--   VCon n us -> case lookupLabel n nass of
--     Just as -> VCon n (transps i as env us)
--     Nothing -> error $ "transpHIT: missing constructor in labelled sum " ++ n
--   VPCon c _ ws0 phis -> case lookupLabel c nass of
--     Just as -> pcon c (a `face` (i ~> 1)) (transps i as env ws0) phis
--     Nothing -> error $ "transpHIT: missing path constructor " ++ c
--   VHComp _ v vs ->
--     hComp (a `face` (i ~> 1)) (transpHIT i a v) $
--       mapWithKey (\alpha vAlpha ->
--                    VPLam j $ transpHIT j (aij `face` alpha) (vAlpha @@ j)) vs
--   _ -> error $ "transpHIT: neutral " ++ show u

-- -- given u(i) of type a(i) "squeezeHIT i a u" connects in the direction i
-- -- transHIT i a u(i=0) to u(i=1) in a(1)
-- squeezeHIT :: Name -> Val -> Val -> Val
-- squeezeHIT i a@(Ter (HSum _ _ nass) env) u =
--  let j = fresh (a,u)
--  in
--  case u of
--   VCon n us -> case lookupLabel n nass of
--     Just as -> VCon n (squeezes i as env us)
--     Nothing -> error $ "squeezeHIT: missing constructor in labelled sum " ++ n
--   VPCon c _ ws0 phis -> case lookupLabel c nass of
--     Just as -> pcon c (a `face` (i ~> 1)) (squeezes i as env ws0) phis
--     Nothing -> error $ "squeezeHIT: missing path constructor " ++ c
--   VHComp _ v vs -> hComp (a `face` (i ~> 1)) (squeezeHIT i a v) $
--       mapWithKey
--         (\alpha vAlpha -> case Map.lookup i alpha of
--           Nothing   -> VPLam j $ squeezeHIT i (a `face` alpha) (vAlpha @@ j)
--           Just Zero -> VPLam j $ transpHIT i
--                          (a `face` (Map.delete i alpha)) (vAlpha @@ j)
--           Just One  -> vAlpha)
--         vs
--   _ -> error $ "squeezeHIT: neutral " ++ show u

-- hComp :: Val -> Val -> System Val -> Val
-- hComp a u us | eps `member` us = (us ! eps) @@ One
--              | otherwise       = VHComp a u us

-------------------------------------------------------------------------------
-- | Glue

-- An equivalence for a type a is a triple (t,f,p) where
-- t : U
-- f : t -> a
-- p : (x : a) -> isContr ((y:t) * Id a x (f y))
-- with isContr c = (z : c) * ((z' : C) -> Id c z z')

-- Extraction functions for getting a, f, s and t:
equivDom :: Val -> Val
equivDom = fstVal

equivFun :: Val -> Val
equivFun = fstVal . sndVal

equivContr :: Val -> Val
equivContr =  sndVal . sndVal

glue :: Val -> System Val -> Val
glue b ts | eps `member` ts = equivDom (ts ! eps)
          | otherwise       = VGlue b ts

glueElem :: Val -> System Val -> Val
glueElem (VUnGlueElem u _) _ = u
glueElem v us | eps `member` us = us ! eps
              | otherwise       = VGlueElem v us

unglueElem :: Val -> System Val -> Val
unglueElem w isos | eps `member` isos = app (equivFun (isos ! eps)) w
                  | otherwise         = case w of
                                          VGlueElem v us -> v
                                          _ -> VUnGlueElem w isos

unGlue :: Val -> Val -> System Val -> Val
unGlue w b equivs | eps `member` equivs = app (equivFun (equivs ! eps)) w
                  | otherwise           = case w of
                                            VGlueElem v us -> v
                                            _ -> error ("unglue: neutral" ++ show w)

-- isNeutralGlue :: Name -> System Val -> Val -> System Val -> Bool
-- isNeutralGlue i equivs u0 ts = (eps `notMember` equivsi0 && isNeutral u0) ||
--   any (\(alpha,talpha) ->
--            eps `notMember` (equivs `face` alpha) && isNeutral talpha)
--     (assocs ts)
--   where equivsi0 = equivs `face` (i ~> 0)

isNeutralGlueHComp :: System Val -> Val -> System Val -> Bool
isNeutralGlueHComp equivs u us =
  (eps `notMember` equivs && isNeutral u) ||
  any (\(alpha,uAlpha) -> eps `notMember` (equivs `face` alpha)
        && isNeutral uAlpha) (assocs us)

-- this is exactly the same as isNeutralGlue?
isNeutralU :: Name -> System Val -> Val -> System Val -> Bool
isNeutralU i eqs u0 ts = (eps `notMember` eqsi0 && isNeutral u0) ||
  any (\(alpha,talpha) ->
           eps `notMember` (eqs `face` alpha) && isNeutral talpha)
    (assocs ts)
  where eqsi0 = eqs `face` (i ~> 0)

-- Extend the system ts to a total element in b given q : isContr b
extend :: Val -> Val -> System Val -> Val
extend b q ts = hComp i b (fstVal q) ts'
  where i = fresh (b,q,ts)
        ts' = mapWithKey
                (\alpha tAlpha -> app ((sndVal q) `face` alpha) tAlpha @@ i) ts

transGlue :: Name -> Val -> System Val -> Formula -> Val -> Val
transGlue i a equivs psi u0 = glueElem v1' t1s'
  where
    v0 = unGlue u0 (a `face` (i ~> 0)) (equivs `face` (i ~> 0))
    ai1 = a `face` (i ~> 1)
    alliequivs = allSystem i equivs
    psisys = invSystem psi One -- (psi = 1) : FF
    t1s = mapWithKey (\al wal -> trans i (equivDom wal) psi (u0 `face` al))
            alliequivs
    wts = mapWithKey (\al wal ->
              app wal (transFill i (equivDom wal) psi (u0 `face` al)))
            alliequivs
    v1 = comp i a v0 (border v0 psisys `unionSystem` wts)

    fibersys = mapWithKey
                 (\al x -> VPair x (constPath (v1 `face` al)))
                 (border u0 psisys `unionSystem` t1s)

    fibersys' = mapWithKey
                  (\al wal ->
                     extend (mkFiberType ai1 (v1 `face` al) wal)
                       (app (equivContr wal) (v1 `face` al))
                       (fibersys `face` al))
                  (equivs `face` (i ~> 1))

    t1s' = Map.map fstVal fibersys'
    -- no need for a fresh name; take i
    v1' = hComp i ai1 v1 (Map.map (\om -> (sndVal om) @@ i) fibersys'
                           `unionSystem` border v1 psisys)

-- -- psi/b corresponds to ws
-- -- b0    corresponds to wi0
-- -- a0    corresponds to vi0
-- -- psi/a corresponds to vs
-- -- a1'   corresponds to vi1'
-- -- equivs' corresponds to delta
-- -- ti1'  corresponds to usi1'
-- compGlue :: Name -> Val -> System Val -> Val -> System Val -> Val
-- compGlue i a equivs wi0 ws = glueElem vi1 usi1
--   where ai1 = a `face` (i ~> 1)
--         vs  = mapWithKey
--                 (\alpha wAlpha ->
--                   unGlue wAlpha (a `face` alpha) (equivs `face` alpha)) ws

--         vsi1 = vs `face` (i ~> 1) -- same as: border vi1 vs
--         vi0  = unGlue wi0 (a `face` (i ~> 0)) (equivs `face` (i ~> 0)) -- in a(i0)

--         vi1'  = comp i a vi0 vs           -- in a(i1)

--         equivsI1 = equivs `face` (i ~> 1)
--         equivs'  = filterWithKey (\alpha _ -> i `notMember` alpha) equivs

--         us'    = mapWithKey (\gamma equivG ->
--                    fill i (equivDom equivG) (wi0 `face` gamma) (ws `face` gamma))
--                  equivs'
--         usi1'  = mapWithKey (\gamma equivG ->
--                    comp i (equivDom equivG) (wi0 `face` gamma) (ws `face` gamma))
--                  equivs'

--         -- path in ai1 between vi1 and f(i1) usi1' on equivs'
--         ls'    = mapWithKey (\gamma equivG ->
--                    pathComp i (a `face` gamma) (vi0 `face` gamma)
--                      (equivFun equivG `app` (us' ! gamma)) (vs `face` gamma))
--                  equivs'

--         fibersys = intersectionWith VPair usi1' ls' -- on equivs'

--         wsi1 = ws `face` (i ~> 1)
--         fibersys' = mapWithKey
--           (\gamma equivG ->
--             let fibsgamma = intersectionWith (\ x y -> VPair x (constPath y))
--                               (wsi1 `face` gamma) (vsi1 `face` gamma)
--             in extend (mkFiberType (ai1 `face` gamma) (vi1' `face` gamma) equivG)
--                  (app (equivContr equivG) (vi1' `face` gamma))
--                  (fibsgamma `unionSystem` (fibersys `face` gamma))) equivsI1

--         vi1 = compConstLine ai1 vi1'
--                 (Map.map sndVal fibersys' `unionSystem` Map.map constPath vsi1)

--         usi1 = Map.map fstVal fibersys'

mkFiberType :: Val -> Val -> Val -> Val
mkFiberType a x equiv = eval rho $
  Sigma $ Lam "y" tt (PathP (PLam (Name "_") ta) tx (App tf ty))
  where [ta,tx,ty,tf,tt] = map Var ["a","x","y","f","t"]
        rho = upds [("a",a),("x",x),("f",equivFun equiv)
                   ,("t",equivDom equiv)] emptyEnv

-- Assumes u' : A is a solution of us + (i0 -> u0)
-- The output is an L-path in A(i1) between comp i u0 us and u'(i1)
pathComp :: Name -> Val -> Val -> Val -> System Val -> Val
pathComp i a u0 u' us = VPLam j $ comp i a u0 us'
  where j   = fresh (Atom i,a,us,u0,u')
        us' = insertsSystem [(j ~> 1, u')] us

-------------------------------------------------------------------------------
-- | Composition in the Universe

-- -- any path between types define an equivalence
-- eqFun :: Val -> Val -> Val
-- eqFun = transNegLine

-- unGlueU :: Val -> Val -> System Val -> Val
-- unGlueU w b es | eps `Map.member` es = eqFun (es ! eps) w
--                | otherwise           = case w of
--                                         VGlueElem v us   -> v
--                                         _ -> VUnGlueElemU w b es

-- -- compUniv :: Val -> System Val -> Val
-- -- compUniv b es | eps `Map.member` es = (es ! eps) @@ One
-- --               | otherwise           = VCompU b es

-- compU :: Name -> Val -> System Val -> Val -> System Val -> Val
-- compU i a eqs wi0 ws = glueElem vi1 usi1
--   where ai1 = a `face` (i ~> 1)
--         vs  = mapWithKey
--                 (\alpha wAlpha ->
--                   unGlueU wAlpha (a `face` alpha) (eqs `face` alpha)) ws

--         vsi1 = vs `face` (i ~> 1) -- same as: border vi1 vs
--         vi0  = unGlueU wi0 (a `face` (i ~> 0)) (eqs `face` (i ~> 0)) -- in a(i0)

--         vi1'  = comp i a vi0 vs           -- in a(i1)

--         eqsI1 = eqs `face` (i ~> 1)
--         eqs'  = filterWithKey (\alpha _ -> i `notMember` alpha) eqs

--         us'    = mapWithKey (\gamma eqG ->
--                    fill i (eqG @@ One) (wi0 `face` gamma) (ws `face` gamma))
--                  eqs'
--         usi1'  = mapWithKey (\gamma eqG ->
--                    comp i (eqG @@ One) (wi0 `face` gamma) (ws `face` gamma))
--                  eqs'

--         -- path in ai1 between vi1 and f(i1) usi1' on eqs'
--         ls'    = mapWithKey (\gamma eqG ->
--                    pathComp i (a `face` gamma) (vi0 `face` gamma)
--                      (eqFun eqG (us' ! gamma)) (vs `face` gamma))
--                  eqs'

--         fibersys = intersectionWith (\ x y -> (x,y)) usi1' ls' -- on eqs'

--         wsi1 = ws `face` (i ~> 1)
--         fibersys' = mapWithKey
--           (\gamma eqG ->
--             let fibsgamma = intersectionWith (\ x y -> (x,constPath y))
--                               (wsi1 `face` gamma) (vsi1 `face` gamma)
--             in lemEq eqG (vi1' `face` gamma)
--                      (fibsgamma `unionSystem` (fibersys `face` gamma))) eqsI1

--         vi1 = compConstLine ai1 vi1'
--                 (Map.map snd fibersys' `unionSystem` Map.map constPath vsi1)

--         usi1 = Map.map fst fibersys'

-- lemEq :: Val -> Val -> System (Val,Val) -> (Val,Val)
-- lemEq eq b aps = (a,VPLam i (compNeg j (eq @@ j) p1 thetas'))
--  where
--    i:j:_ = freshs (eq,b,aps)
--    ta = eq @@ One
--    p1s = mapWithKey (\alpha (aa,pa) ->
--               let eqaj = (eq `face` alpha) @@ j
--                   ba = b `face` alpha
--               in comp j eqaj (pa @@ i)
--                    (mkSystem [ (i~>0,transFill j eqaj ba)
--                              , (i~>1,transFillNeg j eqaj aa)])) aps
--    thetas = mapWithKey (\alpha (aa,pa) ->
--               let eqaj = (eq `face` alpha) @@ j
--                   ba = b `face` alpha
--               in fill j eqaj (pa @@ i)
--                    (mkSystem [ (i~>0,transFill j eqaj ba)
--                              , (i~>1,transFillNeg j eqaj aa)])) aps

--    a  = comp i ta (trans i (eq @@ i) b) p1s
--    p1 = fill i ta (trans i (eq @@ i) b) p1s

--    thetas' = insertsSystem [ (i ~> 0,transFill j (eq @@ j) b)
--                            , (i ~> 1,transFillNeg j (eq @@ j) a)] thetas


-------------------------------------------------------------------------------
-- | Conversion

class Convertible a where
  conv :: [String] -> a -> a -> Bool

isCompSystem :: (Nominal a, Convertible a) => [String] -> System a -> Bool
isCompSystem ns ts = and [ conv ns (getFace alpha beta) (getFace beta alpha)
                         | (alpha,beta) <- allCompatible (keys ts) ]
    where getFace a b = face (ts ! a) (b `minus` a)

instance Convertible Env where
  conv ns (Env (rho1,vs1,fs1,os1)) (Env (rho2,vs2,fs2,os2)) =
      conv ns (rho1,vs1,fs1,os1) (rho2,vs2,fs2,os2)

instance Convertible Val where
  conv ns u v | u == v    = True
              | otherwise =
    let j = fresh (u,v)
    in case (u,v) of
      (Ter (Lam x a u) e,Ter (Lam x' a' u') e') ->
        let v@(VVar n _) = mkVarNice ns x (eval e a)
        in conv (n:ns) (eval (upd (x,v) e) u) (eval (upd (x',v) e') u')
      (Ter (Lam x a u) e,u') ->
        let v@(VVar n _) = mkVarNice ns x (eval e a)
        in conv (n:ns) (eval (upd (x,v) e) u) (app u' v)
      (u',Ter (Lam x a u) e) ->
        let v@(VVar n _) = mkVarNice ns x (eval e a)
        in conv (n:ns) (app u' v) (eval (upd (x,v) e) u)
      (Ter (Split _ p _ _) e,Ter (Split _ p' _ _) e') -> (p == p') && conv ns e e'
      (Ter (Sum p _ _) e,Ter (Sum p' _ _) e')         -> (p == p') && conv ns e e'
      (Ter (HSum p _ _) e,Ter (HSum p' _ _) e')       -> (p == p') && conv ns e e'
      (Ter (Undef p _) e,Ter (Undef p' _) e') -> p == p' && conv ns e e'
      (Ter (Hole p) e,Ter (Hole p') e') -> p == p' && conv ns e e'
      -- (Ter Hole{} e,_) -> True
      -- (_,Ter Hole{} e') -> True
      (VPi u v,VPi u' v') ->
        let w@(VVar n _) = mkVarNice ns "X" u
        in conv ns u u' && conv (n:ns) (app v w) (app v' w)
      (VSigma u v,VSigma u' v') ->
        let w@(VVar n _) = mkVarNice ns "X" u
        in conv ns u u' && conv (n:ns) (app v w) (app v' w)
      (VCon c us,VCon c' us')   -> (c == c') && conv ns us us'
      (VPCon c v us phis,VPCon c' v' us' phis') ->
        (c == c') && conv ns (v,us,phis) (v',us',phis')
      (VPair u v,VPair u' v')    -> conv ns u u' && conv ns v v'
      (VPair u v,w)              -> conv ns u (fstVal w) && conv ns v (sndVal w)
      (w,VPair u v)              -> conv ns (fstVal w) u && conv ns (sndVal w) v
      (VFst u,VFst u')           -> conv ns u u'
      (VSnd u,VSnd u')           -> conv ns u u'
      (VApp u v,VApp u' v')      -> conv ns u u' && conv ns v v'
      (VSplit u v,VSplit u' v')  -> conv ns u u' && conv ns v v'
      (VOpaque x _, VOpaque x' _) -> x == x'
      (VVar x _, VVar x' _)       -> x == x'
      (VPathP a b c,VPathP a' b' c') -> conv ns a a' && conv ns b b' && conv ns c c'
      (VPLam i a,VPLam i' a')    -> conv ns (a `swap` (i,j)) (a' `swap` (i',j))
      (VPLam i a,p')             -> conv ns (a `swap` (i,j)) (p' @@ j)
      (p,VPLam i' a')            -> conv ns (p @@ j) (a' `swap` (i',j))
      (VAppFormula u x,VAppFormula u' x') -> conv ns (u,x) (u',x')
      -- (VComp a u ts,VComp a' u' ts')      -> conv ns (a,u,ts) (a',u',ts')
      (VHComp a u ts,VHComp a' u' ts')    -> conv ns (a,u,ts) (a',u',ts')
      (VGlue v equivs,VGlue v' equivs')   -> conv ns (v,equivs) (v',equivs')
      (VGlueElem u us,VGlueElem u' us')   -> conv ns (u,us) (u',us')
      -- (VUnGlueElemU u _ _,VUnGlueElemU u' _ _) -> conv ns u u'
      (VUnGlueElem u ts,VUnGlueElem u' ts')    -> conv ns (u,ts) (u',ts')
      -- (VCompU u es,VCompU u' es')              -> conv ns (u,es) (u',es')
      (VIdPair v vs,VIdPair v' vs')          -> conv ns (v,vs) (v',vs')
      (VId a u v,VId a' u' v')               -> conv ns (a,u,v) (a',u',v')
      (VIdJ a u c d x p,VIdJ a' u' c' d' x' p') ->
        conv ns [a,u,c,d,x,p] [a',u',c',d',x',p']
      _                                      -> False

instance Convertible Ctxt where
  conv _ _ _ = True

instance Convertible () where
  conv _ _ _ = True

instance (Convertible a, Convertible b) => Convertible (a, b) where
  conv ns (u, v) (u', v') = conv ns u u' && conv ns v v'

instance (Convertible a, Convertible b, Convertible c)
      => Convertible (a, b, c) where
  conv ns (u, v, w) (u', v', w') = conv ns (u,(v,w)) (u',(v',w'))

instance (Convertible a,Convertible b,Convertible c,Convertible d)
      => Convertible (a,b,c,d) where
  conv ns (u,v,w,x) (u',v',w',x') = conv ns (u,v,(w,x)) (u',v',(w',x'))

instance Convertible a => Convertible [a] where
  conv ns us us' = length us == length us' &&
                  and [conv ns u u' | (u,u') <- zip us us']

instance Convertible a => Convertible (System a) where
  conv ns ts ts' = keys ts == keys ts' &&
                   and (elems (intersectionWith (conv ns) ts ts'))

instance Convertible Formula where
  conv _ phi psi = dnf phi == dnf psi

instance Convertible (Nameless a) where
  conv _ _ _ = True

-------------------------------------------------------------------------------
-- | Normalization

class Normal a where
  normal :: [String] -> a -> a

instance Normal Env where
  normal ns (Env (rho,vs,fs,os)) = Env (normal ns (rho,vs,fs,os))

instance Normal Val where
  normal ns v = case v of
    VU                  -> VU
    Ter (Lam x t u) e   ->
      let w = eval e t
          v@(VVar n _) = mkVarNice ns x w
      in VLam n (normal ns w) $ normal (n:ns) (eval (upd (x,v) e) u)
    Ter t e             -> Ter t (normal ns e)
    VPi u v             -> VPi (normal ns u) (normal ns v)
    VSigma u v          -> VSigma (normal ns u) (normal ns v)
    VPair u v           -> VPair (normal ns u) (normal ns v)
    VCon n us           -> VCon n (normal ns us)
    VPCon n u us phis   -> VPCon n (normal ns u) (normal ns us) phis
    VPathP a u0 u1      -> VPathP (normal ns a) (normal ns u0) (normal ns u1)
    VPLam i u           -> VPLam i (normal ns u)
    -- VComp u v vs        -> VComp (normal ns u) (normal ns v) (normal ns vs)
    VHComp u v vs       -> VHComp (normal ns u) (normal ns v) (normal ns vs)
    VGlue u equivs      -> VGlue (normal ns u) (normal ns equivs)
    VGlueElem u us      -> VGlueElem (normal ns u) (normal ns us)
    VUnGlueElem u us    -> VUnGlueElem (normal ns u) (normal ns us)
    -- VUnGlueElemU e u us -> VUnGlueElemU (normal ns e) (normal ns u) (normal ns us)
    -- VCompU a ts         -> VCompU (normal ns a) (normal ns ts)
    VVar x t            -> VVar x (normal ns t)
    VFst t              -> VFst (normal ns t)
    VSnd t              -> VSnd (normal ns t)
    VSplit u t          -> VSplit (normal ns u) (normal ns t)
    VApp u v            -> VApp (normal ns u) (normal ns v)
    VAppFormula u phi   -> VAppFormula (normal ns u) (normal ns phi)
    VId a u v           -> VId (normal ns a) (normal ns u) (normal ns v)
    VIdPair u us        -> VIdPair (normal ns u) (normal ns us)
    VIdJ a u c d x p    -> VIdJ (normal ns a) (normal ns u) (normal ns c)
                                (normal ns d) (normal ns x) (normal ns p)
    _                   -> v

instance Normal (Nameless a) where
  normal _ = id

instance Normal Ctxt where
  normal _ = id

instance Normal Formula where
  normal _ = fromDNF . dnf

instance Normal a => Normal (Map k a) where
  normal ns = Map.map (normal ns)

instance (Normal a,Normal b) => Normal (a,b) where
  normal ns (u,v) = (normal ns u,normal ns v)

instance (Normal a,Normal b,Normal c) => Normal (a,b,c) where
  normal ns (u,v,w) = (normal ns u,normal ns v,normal ns w)

instance (Normal a,Normal b,Normal c,Normal d) => Normal (a,b,c,d) where
  normal ns (u,v,w,x) =
    (normal ns u,normal ns v,normal ns w, normal ns x)

instance Normal a => Normal [a] where
  normal ns = map (normal ns)
