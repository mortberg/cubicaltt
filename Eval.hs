module Eval where

import Data.List
import Data.Maybe (fromMaybe)

import Connections
import CTT

look :: String -> Env -> Val
look x (Pair rho ((y,_),u)) | x == y    = u
                            | otherwise = look x rho
look x r@(PDef es r1) = case lookupIdent x es of
  Just (_,t) -> eval r t
  Nothing -> look x r1

lookType :: String -> Env -> Val
lookType x (Pair rho ((y,_),VVar _ a)) | x == y    = a
                                       | otherwise = lookType x rho
lookType x r@(PDef es r1) = case lookupIdent x es of
  Just (a,_) -> eval r a
  Nothing -> lookType x r1

eval :: Env -> Ter -> Val
eval rho v = case v of
  U                   -> VU
  App r s             -> app (eval rho r) (eval rho s)
  Var i               -> look i rho
  Pi t@(Lam _ a _)    -> VPi (eval rho a) (eval rho t)
  Lam x a t           -> Ter (Lam x a t) rho
  Sigma t@(Lam _ a _) -> VSigma (eval rho a) (eval rho t)
  SPair a b           -> VSPair (eval rho a) (eval rho b)
  Fst a               -> fstVal (eval rho a)
  Snd a               -> sndVal (eval rho a)
  Where t decls       -> eval (PDef decls rho) t
  Con name ts         -> VCon name (map (eval rho) ts)
  Split l t brcs      -> Ter (Split l t brcs) rho
  Sum pr lbls         -> Ter (Sum pr lbls) rho
  Undef l             -> error $ "eval: undefined at " ++ show l
  IdP a e0 e1         -> VIdP (eval rho a) (eval rho e0) (eval rho e1)
  Path i t            -> Ter (Path i t) rho
    -- let j = fresh (t,rho)
    -- in VPath j (eval rho (t `swap` (i,j)))


evals :: Env -> [(Binder,Ter)] -> [(Binder,Val)]
evals env bts = [ (b,eval env t) | (b,t) <- bts ]

app :: Val -> Val -> Val
app (Ter (Lam x _ t) e) u                  = eval (Pair e (x,u)) t
app (Ter (Split _ _ nvs) e) (VCon name us) = case lookup name nvs of
  Just (xs,t) -> eval (pairs e (zip xs us)) t
  Nothing     -> error $ "app: Split with insufficient arguments; " ++
                         " missing case for " ++ name
app u@(Ter (Split _ _ _) _) v | isNeutral v = VSplit u v
app r s | isNeutral r = VApp r s
app _ _ = error "app"

fstVal, sndVal :: Val -> Val
fstVal (VSPair a b)    = a
fstVal u | isNeutral u = VFst u
sndVal (VSPair a b)    = b
sndVal u | isNeutral u = VSnd u

-------------------------------------------------------------------------------
-- | Conversion

conv :: Int -> Val -> Val -> Bool
conv k u v | u == v    = True
           | otherwise = case (u,v) of
  (Ter (Lam x a u) e,Ter (Lam x' a' u') e') -> 
    let v = mkVar k (eval e a)
    in conv (k+1) (eval (Pair e (x,v)) u) (eval (Pair e' (x',v)) u')
  (Ter (Lam x a u) e,u') ->
    let v = mkVar k (eval e a)
    in conv (k+1) (eval (Pair e (x,v)) u) (app u' v)
  (u',Ter (Lam x a u) e) ->
    let v = mkVar k (eval e a)
    in conv (k+1) (app u' v) (eval (Pair e (x,v)) u)
  (Ter (Split p _ _) e,Ter (Split p' _ _) e') -> (p == p') && convEnv k e e'
  (Ter (Sum p _) e,Ter (Sum p' _) e')     -> (p == p') && convEnv k e e'
  (Ter (Undef p) e,Ter (Undef p') e')     -> (p == p') && convEnv k e e'
  (VPi u v,VPi u' v') ->
    let w = mkVar k u
    in conv k u u' && conv (k+1) (app v w) (app v' w)
  (VSigma u v,VSigma u' v') ->
    let w = mkVar k u
    in conv k u u' && conv (k+1) (app v w) (app v' w)
  (VCon c us,VCon c' us')   -> (c == c') && and (zipWith (conv k) us us')
  (VSPair u v,VSPair u' v') -> conv k u u' && conv k v v'
  (VSPair u v,w)            -> conv k u (fstVal w) && conv k v (sndVal w)
  (w,VSPair u v)            -> conv k (fstVal w) u && conv k (sndVal w) v
  (VFst u,VFst u')          -> conv k u u'
  (VSnd u,VSnd u')          -> conv k u u'
  (VApp u v,VApp u' v')     -> conv k u u' && conv k v v'
  (VSplit u v,VSplit u' v') -> conv k u u' && conv k v v'
  (VVar x _, VVar x' _)     -> x == x'
  _                         -> False

convEnv :: Int -> Env -> Env -> Bool
convEnv k e e' = and $ zipWith (conv k) (valOfEnv e) (valOfEnv e')
