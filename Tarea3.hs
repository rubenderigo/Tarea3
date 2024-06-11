module Tarea3 where

import Prelude hiding ((++))

---------------------------------
--Nombre 1	: Leandro Gugiato
--Nro. 1	: 318621
---------------------------------
--Nombre 2 	: Ruben Derigo
--Nro. 2 	: 287176
---------------------------------

--------------------
----Ejercicio 1:----
--------------------
par::Int->Bool
par 0 = True
par k = not (par (k-1))

--1)
prefijo :: (a -> Bool) -> [a] -> [a]
prefijo p [] = []
prefijo p (x:xs)
    | p x = x:(prefijo p xs)
    | otherwise = []

--2)
sufijo :: (a -> Bool) -> [a] -> [a]
sufijo p [] = []
sufijo p (x:xs)
    | p x = sufijo p xs 
    | otherwise = x:xs

(++) :: [a] -> [a] -> [a]
(++) [] k = k
(++) (x:xs) k = x:(xs ++ k)

--3)
{--
(∀ xs::[a]) (∀p::(a−>Bool)) ((prefijo p xs) ++ (sufijo p xs) = xs)
Dmt. por induccion en l::[a]
CB: (∀p::(a− > Bool)) ((prefijo p []) ++ (sufijo p []) = [])
	-------------------------------------------------------------------------------
	| (prefijo p []) ++ (sufijo p []) = prefijo                                   |
	| [] ++ (sufijo p []) =  ++                                                   |
	| sufijo p [] = sufijo                                                        |
	| []                                                                          |
	-------------------------------------------------------------------------------

PI: sea xs::[a]
	H) (∀p::(a− > Bool)) ((prefijo p xs) ++ (sufijo p xs) = xs)
	T) (∀x::a)(∀p::(a−> Bool)) ((prefijo p (x:xs)) ++ (sufijo p (x:xs)) = (x:xs))
	Dmt. por casos en (p x)::Bool
	Caso True: (prefijo p (x:xs)) ++ (sufijo p (x:xs)) = (x:xs)
	-------------------------------------------------------------------------------
	| (prefijo p (x:xs)) ++ (sufijo p (x:xs) = prefijo                            |
	| x:(prefijo p xs) ++ (sufijo p (x:xs) = sufijo                               |
	| x:(prefijo p xs) ++ (sufijo p xs) = ++                                      |
	| x:((prefijo p xs) ++ (sufijo p xs)) = H                                     |
	| x:xs                                                                        |
	-------------------------------------------------------------------------------

	Caso False: (prefijo p (x:xs)) ++ (sufijo p (x:xs)) = (x:xs)
	-------------------------------------------------------------------------------
	|  (prefijo p (x:xs)) ++ (sufijo p (x:xs)) = prefijo                          |
	|  [] ++ (sufijo p (x:xs)) = ++                                               |
	|  sufijo p (x:xs) = sufijo                                                   |
	|  x:xs                                                                       |
	-------------------------------------------------------------------------------

LqqD
-}

--------------------
----Ejercicio 2:----
--------------------

--1)
incluido :: Eq a => [a] -> [a] -> Bool
incluido [] ys = True
incluido (x:xs) ys
    | elem x ys = incluido xs ys 
    | otherwise = False


--2)
interseccion :: Eq a => [a] -> [a] -> [a]
interseccion [] ys = []
interseccion (x:xs) ys
    | elem x ys = x:(interseccion xs ys)
    | otherwise = interseccion xs ys


--3)
{--
(∀ l1,l2::[a]) incluido (interseccion l1 l2) l2 = True
Dmt. por induccion en l1::[a]
CB: (∀ l2::[a]) incluido (interseccion [] l2) l2 = True
 	-------------------------------------------------------------------------------
	| incluido (interseccion [] l2) l2 = interseccion                             |                  
	| incluido [] l2 = incluido                                                   |
	| True                                                                        |
	-------------------------------------------------------------------------------

PI: Sea xs::[a]
	H) (∀ l2::[a]) incluido (interseccion xs l2) l2 = True
	T) (∀ x::a)(∀ l2::[a]) incluido (interseccion (x:xs) l2) l2 = True
	Dmt por Casos en (elem x ys)::Bool
	Caso True: incluido (interseccion (x:xs) l2) l2 = True
	-------------------------------------------------------------------------------
	| incluido (interseccion (x:xs) l2) l2 = interseccion                         |
	| incluido (x:(interseccion xs ys)) l2 = incluido                             |
	| incluido (interseccion xs ys) l2 = H                                        |
	| True                                                                        |
	-------------------------------------------------------------------------------

	Caso False: incluido (interseccion (x:xs) l2) l2 = True
	-------------------------------------------------------------------------------
	| incluido (interseccion (x:xs) l2) l2 = interseccion                         |
	| incluido (interseccion xs ys) l2 = H                                        |
	| True                                                                        |
	-------------------------------------------------------------------------------

LqqD
-}

--------------------
----Ejercicio 3:----
--------------------

data Tree = L Int            -- Hoja c/info::Int
          | U Int Tree       -- Nodo unario c/info::Int
          | B Tree Int Tree  -- Nodo binario c/info::Int

--1)
t :: Tree
t = B (L 4) 8 (U 16 (B (L 9) 14 (L 18)))

--2)
listarElems :: Tree -> [Int]
listarElems (L x) =  x:[]
listarElems (U y t) =  y:(listarElems t)
listarElems (B i s d) =  [s] ++ (listarElems i) ++ (listarElems d)


--3)
esBinario :: Tree -> Bool
esBinario (L x) = True
esBinario (U y t) = False
esBinario (B i s d) = (esBinario i) && (esBinario d)


--4)
espejo :: Tree -> Tree
espejo (L x) = L x
espejo (U y t) = U y (espejo t)
espejo (B i s d) = B (espejo d) s (espejo i)


--5) 
convertirEnBinario :: Tree -> Tree
convertirEnBinario (L x) = L x
convertirEnBinario (U y t) = B (convertirEnBinario t) y (espejo (convertirEnBinario t))
convertirEnBinario (B i s d) = B (convertirEnBinario i) s (convertirEnBinario d)

--6)
{--
Por letra: L1. (∀t::Tree) esBinario t => esBinario (espejo t)

(∀t::Tree) esBinario (convertirEnBinario t) = True
Dmt por induccion de t::Tree
CBL: esBinario (convertirEnBinario (L x)) = True
	-------------------------------------------------------------
	| esBinario (convertirEnBinario (L x)) = convertirEnBinario |
	| esBinario (L x) = esBinario                               |
	| True                                                      |
	-------------------------------------------------------------

PIU: sea g::Tree
	H) esBinario (convertirEnBinario g) = True
	T) (∀x::Int) esBinario (convertirEnBinario (U x g)) = True
	------------------------------------------------------------------------------------------
	| esBinario (convertirEnBinario (U x g)) = convertirEnBinario                            |
	| esBinario (B (convertirEnBinario g) x (espejo (convertirEnBinario g))) = esBinario     |
	| (esBinario (convertirEnBinario g)) && (esBinario (espejo (convertirEnBinario g))) = H  |
	| True && (esBinario (espejo (convertirEnBinario g))) = H, L1                            |
	| True && True = &&                                                                      |
	| True                                                                                   |
	------------------------------------------------------------------------------------------

PIB: sea i,d::Tree
	H1) esBinario (convertirEnBinario i) = True
	H2) esBinario (convertirEnBinario d) = True
	T) (∀x::Int) esBinario (convertirEnBinario (B i x d)) = True
	----------------------------------------------------------------------------------
	| esBinario (convertirEnBinario (B i x d)) = convertirEnBinario                  |
	| esBinario (B (convertirEnBinario i) s (convertirEnBinario d)) = esBinario      |
	| (esBinario (convertirEnBinario i)) && (esBinario (convertirEnBinario d)) = H1  |
	| True && (esBinario (convertirEnBinario d)) = H2                                |
	| True && True = (&&)                                                            |
	| True                                                                           |
	----------------------------------------------------------------------------------

LqqD
--}
