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
    VComp a u ts            -> support (a,u,ts)
    VPathP a v0 v1          -> support [a,v0,v1]
    VPLam i v               -> i `delete` support v
    VSigma u v              -> support (u,v)
    VPair u v               -> support (u,v)
    VFst u                  -> support u
    VSnd u                  -> support u
    VCon _ vs               -> support vs
    VPCon _ a vs phis       -> support (a,vs,phis)
    VHComp a u ts           -> support (a,u,ts)
    VVar _ v                -> support v
    VOpaque _ v             -> support v
    VApp u v                -> support (u,v)
    VLam _ u v              -> support (u,v)
    VAppFormula u phi       -> support (u,phi)
    VSplit u v              -> support (u,v)
    VGlue a ts              -> support (a,ts)
    VGlueElem a ts          -> support (a,ts)
    VUnGlueElem a ts        -> support (a,ts)
    VCompU a ts             -> support (a,ts)
    VUnGlueElemU a b es     -> support (a,b,es)
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
         VComp a v ts -> compLine (acti a) (acti v) (acti ts)
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
         VHComp a u us           -> hComp (acti a) (acti u) (acti us)
         VVar x v                -> VVar x (acti v)
         VOpaque x v             -> VOpaque x (acti v)
         VAppFormula u psi       -> acti u @@ acti psi
         VApp u v                -> app (acti u) (acti v)
         VLam x t u              -> VLam x (acti t) (acti u)
         VSplit u v              -> app (acti u) (acti v)
         VGlue a ts              -> glue (acti a) (acti ts)
         VGlueElem a ts          -> glueElem (acti a) (acti ts)
         VUnGlueElem a ts        -> unglueElem (acti a) (acti ts)
         VUnGlueElemU a b es     -> unGlueU (acti a) (acti b) (acti es)
         VCompU a ts             -> compUniv (acti a) (acti ts)
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
         VComp a v ts            -> VComp (sw a) (sw v) (sw ts)
         VPathP a u v            -> VPathP (sw a) (sw u) (sw v)
         VPLam k v               -> VPLam (swapName k ij) (sw v)
         VSigma a f              -> VSigma (sw a) (sw f)
         VPair u v               -> VPair (sw u) (sw v)
         VFst u                  -> VFst (sw u)
         VSnd u                  -> VSnd (sw u)
         VCon c vs               -> VCon c (sw vs)
         VPCon c a vs phis       -> VPCon c (sw a) (sw vs) (sw phis)
         VHComp a u us           -> VHComp (sw a) (sw u) (sw us)
         VVar x v                -> VVar x (sw v)
         VOpaque x v             -> VOpaque x (sw v)
         VAppFormula u psi       -> VAppFormula (sw u) (sw psi)
         VApp u v                -> VApp (sw u) (sw v)
         VLam x u v              -> VLam x (sw u) (sw v)
         VSplit u v              -> VSplit (sw u) (sw v)
         VGlue a ts              -> VGlue (sw a) (sw ts)
         VGlueElem a ts          -> VGlueElem (sw a) (sw ts)
         VUnGlueElem a ts        -> VUnGlueElem (sw a) (sw ts)
         VUnGlueElemU a b es     -> VUnGlueElemU (sw a) (sw b) (sw es)
         VCompU a ts             -> VCompU (sw a) (sw ts)
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
  (Ter (Lam x _ t) e,_)               -> eval (upd (x,v) e) t
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
  (Ter Split{} _,_) | isNeutral v         -> VSplit u v
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
  VComp a _ _ -> a @@ One
--  VUnGlueElem _ b _  -> b   -- This is wrong! Store the type??
  VUnGlueElemU _ b _ -> b
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

comp :: Name -> Val -> Val -> System Val -> Val
comp i a u ts | eps `member` ts = (ts ! eps) `face` (i ~> 1)
comp i a u ts = VComp (VPLam i a) u (Map.map (VPLam i) ts)

compNeg :: Name -> Val -> Val -> System Val -> Val
compNeg i a u ts = comp i (a `sym` i) u (ts `sym` i)

compLine :: Val -> Val -> System Val -> Val
compLine a u ts = comp i (a @@ i) u (Map.map (@@ i) ts)
  where i = fresh (a,u,ts)

compConstLine :: Val -> Val -> System Val -> Val
compConstLine a u ts = comp i a u (Map.map (@@ i) ts)
  where i = fresh (a,u,ts)

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


-----------------------------------------------------------
-- Transport and squeeze (defined using comp)

trans :: Name -> Val -> Val -> Val
trans i v0 v1 = comp i v0 v1 empty

transNeg :: Name -> Val -> Val -> Val
transNeg i a u = trans i (a `sym` i) u

transLine :: Val -> Val -> Val
transLine u v = trans i (u @@ i) v
  where i = fresh (u,v)

transNegLine :: Val -> Val -> Val
transNegLine u v = transNeg i (u @@ i) v
  where i = fresh (u,v)

-- TODO: define in terms of comps?
transps :: Name -> [(Ident,Ter)] -> Env -> [Val] -> [Val]
transps i []         _ []     = []
transps i ((x,a):as) e (u:us) =
  let v   = transFill i (eval e a) u
      vi1 = trans i (eval e a) u
      vs  = transps i as (upd (x,v) e) us
  in vi1 : vs
transps _ _ _ _ = error "transps: different lengths of types and values"

transFill :: Name -> Val -> Val -> Val
transFill i a u = fill i a u empty

transFillNeg :: Name -> Val -> Val -> Val
transFillNeg i a u = (transFill i (a `sym` i) u) `sym` i

-- Given u of type a "squeeze i a u" connects in the direction i
-- trans i a u(i=0) to u(i=1)
squeeze :: Name -> Val -> Val -> Val
squeeze i a u = comp j (a `disj` (i,j)) u $ mkSystem [ (i ~> 1, ui1) ]
  where j   = fresh (Atom i,a,u)
        ui1 = u `face` (i ~> 1)

squeezes :: Name -> [(Ident,Ter)] -> Env -> [Val] -> [Val]
squeezes i xas e us = comps j xas (e `disj` (i,j)) us'
  where j   = fresh (us,e,Atom i)
        us' = [ (mkSystem [(i ~> 1, u `face` (i ~> 1))],u) | u <- us ]


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

hComp :: Val -> Val -> System Val -> Val
hComp a u us | eps `member` us = (us ! eps) @@ One
             | otherwise       = VHComp a u us

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
glueElem v us | eps `member` us = us ! eps
glueElem v us = VGlueElem v us

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

-------------------------------------------------------------------------------
-- | Composition in the Universe

-- any path between types define an equivalence
eqFun :: Val -> Val -> Val
eqFun = transNegLine

unGlueU :: Val -> Val -> System Val -> Val
unGlueU w b es | eps `Map.member` es = eqFun (es ! eps) w
               | otherwise           = case w of
                                        VGlueElem v us   -> v
                                        _ -> VUnGlueElemU w b es

compUniv :: Val -> System Val -> Val
compUniv b es | eps `Map.member` es = (es ! eps) @@ One
              | otherwise           = VCompU b es

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
      (VComp a u ts,VComp a' u' ts')      -> conv ns (a,u,ts) (a',u',ts')
      (VHComp a u ts,VHComp a' u' ts')    -> conv ns (a,u,ts) (a',u',ts')
      (VGlue v equivs,VGlue v' equivs')   -> conv ns (v,equivs) (v',equivs')
      (VGlueElem (VUnGlueElem b equivs) ts,g) -> conv ns (border b equivs,b) (ts,g)
      (g,VGlueElem (VUnGlueElem b equivs) ts) -> conv ns (border b equivs,b) (ts,g)
      (VGlueElem (VUnGlueElemU b _ equivs) ts,g) -> conv ns (border b equivs,b) (ts,g)
      (g,VGlueElem (VUnGlueElemU b _ equivs) ts) -> conv ns (border b equivs,b) (ts,g)
      (VGlueElem u us,VGlueElem u' us')   -> conv ns (u,us) (u',us')
      (VUnGlueElemU u _ _,VUnGlueElemU u' _ _) -> conv ns u u'
      (VUnGlueElem u _,VUnGlueElem u' _) -> conv ns u u'
      (VCompU u es,VCompU u' es')              -> conv ns (u,es) (u',es')
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
    VComp u v vs        -> VComp (normal ns u) (normal ns v) (normal ns vs)
    VHComp u v vs       -> VHComp (normal ns u) (normal ns v) (normal ns vs)
    VGlue u equivs      -> VGlue (normal ns u) (normal ns equivs)
    VGlueElem u us      -> VGlueElem (normal ns u) (normal ns us)
    VUnGlueElem u us    -> VUnGlueElem (normal ns u) (normal ns us)
    VUnGlueElemU e u us -> VUnGlueElemU (normal ns e) (normal ns u) (normal ns us)
    VCompU a ts         -> VCompU (normal ns a) (normal ns ts)
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
