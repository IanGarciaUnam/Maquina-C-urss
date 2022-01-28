module TinyC where 
 import Data.Maybe
 
 type Identificador = String

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
 trans (E (Top (VardecM id) p) l g (Left (Num n))) = case look g id of
    Just val -> error "La variable ya había sido definida"
    Nothing -> E p l (As (id, N n) g) (Right MtP)
 trans (E (Top (VardecM id) p) l g (Left (Bo b))) = case look g id of
    Just val -> error "La variable ya había sido definida"
    Nothing -> E p l (As (id, B b) g) (Right MtP)
 trans (E (Top (VardecM id) p) l g (Left (Fun lid stm))) = case look g id of
    Just val -> error "La variable ya había sido definida"
    Nothing -> E p l (As (id, F lid stm) g) (Right MtP)
 trans (E p l g (Right (Fundec id li stm))) = E p l (As (id, F li stm) g) (Right MtP)
 
 -- Asignaciones
 trans (E p l g (Right (Asig id exp))) = E (Top (AsigM id) p) l g (Left exp)
 trans (E (Top (AsigM id) p) l g (Left (Num n))) = case change g id (N n) of
    Just gprime -> E p l gprime (Right MtP)
    Nothing -> case change l id (N n) of
       Just lprime -> E p lprime g (Right MtP)
       Nothing -> error "La variable no había sido definida."
 trans (E (Top (AsigM id) p) l g (Left (Bo b))) = case change g id (B b) of
    Just gprime -> E p l gprime (Right MtP)
    Nothing -> case change l id (B b) of
       Just lprime -> E p lprime g (Right MtP)
       Nothing -> error "La variable no había sido definida."
 trans (E (Top (AsigM id) p) l g (Left (Fun lid stm))) = case change g id (F lid stm) of
    Just gprime -> E p l gprime (Right MtP)
    Nothing -> case change l id (F lid stm) of
       Just lprime -> E p lprime g (Right MtP)
       Nothing -> error "La variable no había sido definida."
 
 -- Variables
 trans (E p g l (Left (Id id))) = case look g id of
    Just (N n) -> E p g l (Left (Num n))
    Just (B b) -> E p g l (Left (Bo b))
    Just (F lid stm) -> E p g l (Left (Fun lid stm))
    Nothing -> case look l id of
      Just (N n) -> E p g l (Left (Num n))
      Just (B b) -> E p g l (Left (Bo b))
      Just (F lid stm) -> E p g l (Left (Fun lid stm))
      Nothing -> error "La variable no esta definida."

 -- Secuencia
 trans (E p l g (Right (Secu s1 s2))) = E (Top (SecuM s2) p) l g (Right s1)
 trans (E (Top (SecuM s2) p) l g (Right MtP)) = E p l g (Right s2)

 -- Condicionales
 trans (E p l g (Right (If exp s1 s2))) = E (Top (IfM s1 s2) p) l g (Left exp)
 trans (E (Top (IfM s1 s2) p) l g (Left exp))
   | exp == Bo True = E p l g (Right s1)
   | exp == Bo False = E p l g (Right s2)
   | otherwise = error "La guarda del if es inválida."
 trans (E p l g (Right (IfO exp stm))) = E (Top (IfOM stm) p) l g (Left exp)
 trans (E (Top (IfOM stm) p) l g (Left exp))
   | exp == Bo True = E p l g (Right stm)
   | exp == Bo False = E p l g (Right MtP)
   | otherwise = error "La guarda del if es inválida."

 -- Momentaneo
 trans _ = error "Estado inválido"