module TinyC where 
 import Data.Maybe
 
 type Identificador = String

 {-
   En el caso de las llamadas a función hay un problema.

   Necesitamos el precerbar de alguna forma las expresiones que queremos asociar con los parametros
   de la función, esto en la nota se hace mediante el marco que guarda en la pila el momento en el
   que se hace una llamada a función. Sin embargo, en esta implementación no contiene dicha informa-
   ción. Por lo que se buscaron diferentes soluciones que pudieran resolve el problema. Entonces se
   proponen 3 posibles:

   1. Se define una versión alterativa en donde el marco guarda la información de las expresiones.
   2. Se define una función auxiliar para poder evluar las expresiones hasta llevarlas a un valor.
   3. Se presupone que en la llamada, ya todas las expresiones son valores.
 -}

 -- Expresiones
 data Expr = Num Int
            | Bo Bool
            | Id Identificador
            | Fun [Identificador] Stmt
            | Suma Expr Expr
            | Resta Expr Expr
            | Gt Expr Expr
            | Lt Expr Expr
            | Funcall Identificador [Expr]
            deriving(Show,Eq)
 -- Comandos 
 data Stmt = Vardec Identificador Expr
            | Fundec Identificador [Identificador] Stmt
            | Asig Identificador Expr
            | Secu Stmt Stmt
            | If Expr Stmt Stmt
            | IfO Expr Stmt
            | While Expr Stmt 
            | Return Expr
            | MtP
            deriving(Show,Eq)

 type Program = Either Expr Stmt

 -- Valores para almacenar en el ambiente
 data Value = N Int | B Bool | F [Identificador] Stmt deriving(Show,Eq)

-- Sinónimo para definir los pares de variables con su valor que se almacenan en el ambiente
 type Var = (Identificador,Value)

-- Ambientes
 data Env = MtEnv | As Var Env | Star Env Env deriving(Show,Eq)

-- Marcos de la pila

 {-
   Definición alternativa para los marcos de llamada a función, en esta versión se maneja una lista de
   expresiones en conjunto con el identificador de la función.

 data Marco = VardecM Identificador
            | AsigM Identificador
            | SecuM Stmt
            | IfM Stmt Stmt
            | IfOM Stmt
            | ReturnM 
            | FuncallM Identificador [Epr]
            deriving(Show,Eq)
 -}
 data Marco = VardecM Identificador
            | AsigM Identificador
            | SecuM Stmt
            | IfM Stmt Stmt
            | IfOM Stmt
            | ReturnM 
            | FuncallM Identificador
            deriving(Show,Eq) 

-- Pila de control
 data Pila = Mt | Top Marco Pila deriving(Show,Eq)

-- Estados de la Máquina C
 data State = E Pila Env Env Program | R Pila Env Env Program deriving(Show,Eq)


-- Función look que busca un identificador en el ambiente
 look :: Env -> Identificador -> Maybe Value
 look MtEnv _ = Nothing
 look (As (id, val) env) x
    | x == id = Just val
    | otherwise = look env x
 look (Star env1 env2) x
    | look env1 x == Nothing = look env2 x
    | otherwise = look env1 x

-- Función look que modifica el valor asociado a un identificador en el ambiente
 change :: Env -> Identificador -> Value -> Maybe Env
 change MtEnv _ _ = Nothing
 change (As (id, val) env) x v
    | id == x = Just (As (id, v) env)
    | otherwise = change env x v
 change (Star env1 env2) x v
    | change env1 x v == Nothing = change env2 x v
    | otherwise = change env1 x v

-- Función trans que define el sistema de transiciones
 trans :: State -> State
 
 -- Declaraciones
 trans (E p l g (Right (Vardec id exp))) = E (Top (VardecM id) p) l g (Left exp)
 trans (R (Top (VardecM id) p) l g (Left (Num n))) = case look g id of
    Just val -> error "La variable ya había sido definida"
    Nothing -> R p l (As (id, N n) g) (Right MtP)
 trans (R (Top (VardecM id) p) l g (Left (Bo b))) = case look g id of
    Just val -> error "La variable ya había sido definida"
    Nothing -> R p l (As (id, B b) g) (Right MtP)
 trans (R (Top (VardecM id) p) l g (Left (Fun lid stm))) = case look g id of
    Just val -> error "La variable ya había sido definida"
    Nothing -> R p l (As (id, F lid stm) g) (Right MtP)
 trans (E p l g (Right (Fundec id li stm))) = R p l (As (id, F li stm) g) (Right MtP)
 
 -- Asignaciones
 trans (E p l g (Right (Asig id exp))) = E (Top (AsigM id) p) l g (Left exp)
 trans (R (Top (AsigM id) p) l g (Left (Num n))) = case change g id (N n) of
    Just gprime -> R p l gprime (Right MtP)
    Nothing -> case change l id (N n) of
       Just lprime -> R p lprime g (Right MtP)
       Nothing -> error "La variable no había sido definida."
 trans (R (Top (AsigM id) p) l g (Left (Bo b))) = case change g id (B b) of
    Just gprime -> R p l gprime (Right MtP)
    Nothing -> case change l id (B b) of
       Just lprime -> R p lprime g (Right MtP)
       Nothing -> error "La variable no había sido definida."
 trans (R (Top (AsigM id) p) l g (Left (Fun lid stm))) = case change g id (F lid stm) of
    Just gprime -> R p l gprime (Right MtP)
    Nothing -> case change l id (F lid stm) of
       Just lprime -> R p lprime g (Right MtP)
       Nothing -> error "La variable no había sido definida."
 
 -- Variables
 trans (E p g l (Left (Id id))) = case look g id of
    Just (N n) -> R p g l (Left (Num n))
    Just (B b) -> R p g l (Left (Bo b))
    Just (F lid stm) -> R p g l (Left (Fun lid stm))
    Nothing -> case look l id of
      Just (N n) -> R p g l (Left (Num n))
      Just (B b) -> R p g l (Left (Bo b))
      Just (F lid stm) -> R p g l (Left (Fun lid stm))
      Nothing -> error "La variable no esta definida."

 -- Secuencia
 trans (E p l g (Right (Secu s1 s2))) = E (Top (SecuM s2) p) l g (Right s1)
 trans (R (Top (SecuM s2) p) l g (Right MtP)) = E p l g (Right s2)

 -- Condicionales
 trans (E p l g (Right (If exp s1 s2))) = E (Top (IfM s1 s2) p) l g (Left exp)
 trans (R (Top (IfM s1 s2) p) l g (Left exp))
   | exp == Bo True = E p l g (Right s1)
   | exp == Bo False = E p l g (Right s2)
   | otherwise = error "La guarda del if es inválida."
 trans (E p l g (Right (IfO exp stm))) = E (Top (IfOM stm) p) l g (Left exp)
 trans (R (Top (IfOM stm) p) l g (Left exp))
   | exp == Bo True = E p l g (Right stm)
   | exp == Bo False = R p l g (Right MtP)
   | otherwise = error "La guarda del if es inválida."

 -- While
 trans (E p l g (Right (While exp stm))) = E p l g (Right (IfO exp (Secu stm (While exp stm))))

 -- Llamadas a función
 {-
   Versión con la definición alternativa del marco para llamadas a función.

 trans (E p l g (Left (Funcall id []))) = case look g id of
    Just (F lid stm) -> E p (Star g l) l (Right stm)
    _ -> error "La función llamada, no ha sido definida."
 trans (E p l g (Left (Funcall id (e:lexp)))) = case look g id of
    Just (F lid stm) -> E (Top (FuncallM id lexp) p) (As (id, F lid stm) l) g (Left e)
    _ -> error "La función llamada, no ha sido definida."
 trans (R (Top (FuncallM id1 []) p) (As (id2, F (i:lid) stm) l) g (Left v)) = case v of
    Num n -> E p (Star g l) (As (i, N n) l) (Right stm)
    Bo b -> E p (Star g l) (As (i, B b) l) (Right stm)
    Fun li st -> E p (Star g l) (As (i, F li st) l) (Right stm)
    _ -> error "Un paramétro de la llamada, no es un valor."
 trans (R (Top (FuncallM id1 (e:lexp)) p) (As (id2, F (i:lid) stm) l) g (Left v)) = case v of
    Num n -> E (Top (FuncallM id1 lexp) p) (As (id2, F lid stm) (As (i, N n) l)) g (Left e)
    Bo b -> E (Top (FuncallM id1 lexp) p) (As (id2, F lid stm) (As (i, B b) l)) g (Left e)
    Fun li stm -> E (Top (FuncallM id1 lexp) p) (As (id2, F lid stm) (As (i, F li stm) l)) g (Left e)
    _ -> error "Un paramétro de la llamada, no es un valor."
 -}

 {-
   Versíon usando la alternativa de una función auxiliar.

 trans s@(E p g l (Left (Funcall id exprs))) = case look g id of
    Just (F ids stm) -> transFun s ids MtEnv stm
    _ -> error "La función llamada, no ha sido definida."
 -}

 {-
   Función usando el hecho de que todas las expresiones listadas son un valor.
 -}
 trans (E p l g (Left (Funcall id exprs))) = case look g id of
    Just (F ids stm) -> R (Top (FuncallM id) p) l (As (id, F ids stm) g) (Left (Funcall id exprs))
    _ -> error "La función llamada, no ha sido definida."
 trans (R (Top (FuncallM id1) p) l (As (id2, F ids stm) g) (Left (Funcall id3 []))) = E p (Star g l) l (Right  stm)
 trans (R (Top (FuncallM id1) p) l (As (id2, F (i:ids) stm) g) (Left (Funcall id3 (e : exprs)))) = case e of
    Num n -> R (Top (FuncallM id1) p) (As (i, N n) l) (As (id2, F ids stm) g) (Left (Funcall id3 exprs))
    Bo b -> R (Top (FuncallM id1) p) (As (i, B b) l) (As (id2, F ids stm) g) (Left (Funcall id3 exprs))
    Fun li st -> R (Top (FuncallM id1) p) (As (i, F li st) l) (As (id2, F ids stm) g) (Left (Funcall id3 exprs))
    _ -> error "Uno de los paramétros de la llamada no es un valor."

 -- Return
 trans (E p g l (Right (Return exp))) = E (Top ReturnM p) g l (Left exp)
 trans (R (Top ReturnM p) (Star g l1) l2 e@(Left (Num n))) = R p l1 g e
 trans (R (Top ReturnM p) (Star g l1) l2 e@(Left (Bo b))) = R p l1 g e
 trans (R (Top ReturnM p) (Star g l1) l2 e@(Left (Fun id stm))) = R p l1 g e

 -- Momentaneo
 trans _ = error "Estado inválido"

 {-
   Función auxiliar para resolver las transiciones en funciones.
 -}
 transFun :: State -> [Identificador] -> Env -> Stmt -> State
 transFun (E p l g (Left (Funcall id []))) i env stm = E p (Star g l) env (Right stm)
 transFun (E p l g (Left (Funcall id (e : le)))) (i : ids) env stm = case trans (E p l g (Left e)) of
    (E p g l (Left val)) -> case val of
       Num n -> transFun (E p l g (Left (Funcall id le))) ids (As (i, N n) env) stm
       Bo b -> transFun (E p l g (Left (Funcall id le))) ids (As (i, B b) env) stm
       Fun lids stm2 -> transFun (E p l g (Left (Funcall id le))) ids (As (i, F lids stm2) env) stm
       _ -> error "Uno de los parametros no puede ser reducido a un vamor"
    _ -> error "Fallo en la evaluación"
 transFun _ _ _ _ = error ""