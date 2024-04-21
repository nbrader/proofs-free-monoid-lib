#!/usr/bin/env stack
-- stack --resolver lts-20.5 ghci --package QuickCheck-2.14.2

import Data.Monoid
import Data.Foldable
import Test.QuickCheck
import Data.Bits

type Basis2 = Bool
class (Monoid m) => FreeMonoid2 m where
    canonicalInj :: Basis2 -> m

-- Monoid properties
-- Left Identity
prop_leftIdentity :: (Eq m, Monoid m, Show m) => m -> Property
prop_leftIdentity x = mempty <> x === x

-- Right Identity
prop_rightIdentity :: (Eq m, Monoid m, Show m) => m -> Property
prop_rightIdentity x = x <> mempty === x

-- Associativity
prop_associativity :: (Eq m, Monoid m, Show m) => m -> m -> m -> Property
prop_associativity x y z = (x <> y) <> z === x <> (y <> z)


-- Homomorphism Properties
-- Identity Preservation Property
prop_identityPreservation :: (Monoid a, Monoid b, Eq b, Show b) => (a -> b) -> Property
prop_identityPreservation homomorphism =
  homomorphism mempty === mempty

-- Operation Preservation Property
prop_operationPreservation :: (Monoid a, Monoid b, Eq b, Show b) => (a -> b) -> a -> a -> Property
prop_operationPreservation homomorphism x y =
  homomorphism (x <> y) === (homomorphism x <> homomorphism y)

-- Universal Property (Commuting triangle)
prop_universal_property_commuting :: (Eq a, Show a, FreeMonoid2 f) => (Basis2 -> a) -> (f -> a) -> Basis2 -> Property
prop_universal_property_commuting testMap homomorphism = commutesOnInput
  where commutesOnInput input = testMap input === (homomorphism . canonicalInj) input

prop_equal_on_generators :: (Eq a, Show a, FreeMonoid2 f) => (f -> a) -> (f -> a) -> Basis2 -> Property
prop_equal_on_generators homomorphism1 homomorphism2 = commutesOnInput
  where commutesOnInput input = (homomorphism1 . canonicalInj) input === (homomorphism2 . canonicalInj) input

prop_unique_universal_morphism :: (Eq a, Show a) => (t -> a) -> (t -> a) -> t -> Property
prop_unique_universal_morphism morphism1 morphism2 input = (morphism1 input === morphism2 input)


----------------------------
-- (Testing for Freeness) --
----------------------------
------ Maybe [Bool] --------
----------------------------
instance FreeMonoid2 (Maybe [Bool]) where
    canonicalInj :: Basis2 -> Maybe [Bool]
    canonicalInj False = Just [False]
    canonicalInj True  = Just [True]

maybeBoolList_IsNotFree_Proof1 :: IO ()
maybeBoolList_IsNotFree_Proof1 = do
    putStrLn "Testing Maybe [Bool] for monoid laws:"
    quickCheck (prop_leftIdentity :: Maybe [Bool] -> Property)
    quickCheck (prop_rightIdentity :: Maybe [Bool] -> Property)
    quickCheck (prop_associativity :: Maybe [Bool] -> Maybe [Bool] -> Maybe [Bool] -> Property)
    putStr "\n"

    putStrLn "Testing Any for monoid laws:"
    quickCheck (prop_leftIdentity :: Any -> Property)
    quickCheck (prop_rightIdentity :: Any -> Property)
    quickCheck (prop_associativity :: Any -> Any -> Any -> Property)
    putStr "\n"

    putStrLn "Testing homomorphism properties Maybe [Bool] To Any:"
    quickCheck (prop_identityPreservation maybeBoolListToAny1)
    quickCheck (prop_identityPreservation maybeBoolListToAny2)
    quickCheck (prop_operationPreservation maybeBoolListToAny1)
    quickCheck (prop_operationPreservation maybeBoolListToAny2)
    putStr "\n"

    putStrLn "Testing prop_universal_property_commuting for g and maybeBoolListToAny1"
    quickCheck (prop_universal_property_commuting g maybeBoolListToAny1)
    putStr "\n"

    putStrLn "Testing prop_universal_property_commuting for g and maybeBoolListToAny2"
    quickCheck (prop_universal_property_commuting g maybeBoolListToAny2)
    putStr "\n"

    putStrLn "Testing if homomorphism is non-unique:"
    quickCheck (prop_equal_on_generators maybeBoolListToAny1 maybeBoolListToAny2)
    quickCheck (prop_unique_universal_morphism maybeBoolListToAny1 maybeBoolListToAny2 :: Maybe [Bool] -> Property)
    putStr "\n"
    putStr "\n"
  where -- g is a counter example to any g between sets Basis -> UnderlyingSetOf SomeMonoid having a unique homomorphism (where SomeMonoid = Any)
        g :: Basis2 -> Any
        g False = Any True
        g True  = Any True
        
        maybeBoolListToAny1 :: Maybe [Bool] -> Any
        maybeBoolListToAny1 Nothing   = Any False
        maybeBoolListToAny1 (Just []) = Any False
        maybeBoolListToAny1 (Just xs) = Any True
        
        maybeBoolListToAny2 :: Maybe [Bool] -> Any
        maybeBoolListToAny2 Nothing   = Any False
        maybeBoolListToAny2 (Just []) = Any True
        maybeBoolListToAny2 (Just xs) = Any True

maybeBoolList_IsNotFree_Proof2 :: IO ()
maybeBoolList_IsNotFree_Proof2 = do
    putStrLn "Testing Maybe [Bool] for monoid laws:"
    quickCheck (prop_leftIdentity :: Maybe [Bool] -> Property)
    quickCheck (prop_rightIdentity :: Maybe [Bool] -> Property)
    quickCheck (prop_associativity :: Maybe [Bool] -> Maybe [Bool] -> Maybe [Bool] -> Property)
    putStr "\n"
    
    putStrLn "Testing Maybe [Bool] for monoid laws:"
    quickCheck (prop_leftIdentity :: Maybe [Bool] -> Property)
    quickCheck (prop_rightIdentity :: Maybe [Bool] -> Property)
    quickCheck (prop_associativity :: Maybe [Bool] -> Maybe [Bool] -> Maybe [Bool] -> Property)
    putStr "\n"

    putStrLn "Testing homomorphism properties Maybe [Bool] To Maybe [Bool]:"
    quickCheck (prop_identityPreservation maybeBoolListToMaybeBoolList1)
    quickCheck (prop_identityPreservation maybeBoolListToMaybeBoolList2)
    quickCheck (prop_operationPreservation maybeBoolListToMaybeBoolList1)
    quickCheck (prop_operationPreservation maybeBoolListToMaybeBoolList2)
    putStr "\n"

    putStrLn "Testing prop_universal_property_commuting for testMap1 and maybeBoolListToMaybeBoolList1"
    quickCheck (prop_universal_property_commuting testMap1 maybeBoolListToMaybeBoolList1)
    putStr "\n"

    putStrLn "Testing prop_universal_property_commuting for testMap1 and maybeBoolListToMaybeBoolList2"
    quickCheck (prop_universal_property_commuting testMap1 maybeBoolListToMaybeBoolList2)
    putStr "\n"

    putStrLn "Testing if homomorphism is non-unique:"
    quickCheck (prop_equal_on_generators maybeBoolListToMaybeBoolList1 maybeBoolListToMaybeBoolList2)
    quickCheck (prop_unique_universal_morphism maybeBoolListToMaybeBoolList1 maybeBoolListToMaybeBoolList2 :: Maybe [Bool] -> Property)
    putStr "\n"
    putStr "\n"
  where testMap1 :: Basis2 -> Maybe [Bool]
        testMap1 False = Just [False]
        testMap1 True  = Just [True]
        
        maybeBoolListToMaybeBoolList1 :: Maybe [Bool] -> Maybe [Bool]
        maybeBoolListToMaybeBoolList1 Nothing   = Nothing
        maybeBoolListToMaybeBoolList1 (Just []) = Nothing
        maybeBoolListToMaybeBoolList1 (Just xs) = Just xs

        maybeBoolListToMaybeBoolList2 :: Maybe [Bool] -> Maybe [Bool]
        maybeBoolListToMaybeBoolList2 Nothing   = Nothing
        maybeBoolListToMaybeBoolList2 (Just []) = Just []
        maybeBoolListToMaybeBoolList2 (Just xs) = Just xs


----------------------------
-- (Testing for Freeness) --
----------------------------
--------- [Bool] -----------
----------------------------

instance FreeMonoid2 [Bool] where
    canonicalInj :: Basis2 -> [Bool]
    canonicalInj False = [False]
    canonicalInj True  = [True]

type UnderLyingSetOfAny = Bool
boolList_IsFree_For_Any :: IO ()
boolList_IsFree_For_Any = do
    putStrLn "Testing [Bool] for monoid laws:"
    quickCheck (prop_leftIdentity :: [Bool] -> Property)
    quickCheck (prop_rightIdentity :: [Bool] -> Property)
    quickCheck (prop_associativity :: [Bool] -> [Bool] -> [Bool] -> Property)
    putStr "\n"

    putStrLn "Testing Any for monoid laws:"
    quickCheck (prop_leftIdentity :: Any -> Property)
    quickCheck (prop_rightIdentity :: Any -> Property)
    quickCheck (prop_associativity :: Any -> Any -> Any -> Property)
    putStr "\n"

    putStrLn "Testing homomorphism properties [Bool] To Any:"
    sequence $ [quickCheck (prop_identityPreservation boolListToAny) | boolMap <- allBoolMaps, let testMap = Any . boolMap, let boolListToAny = foldMap Any . map boolMap]
    sequence $ [quickCheck (prop_operationPreservation boolListToAny) | boolMap <- allBoolMaps, let testMap = Any . boolMap, let boolListToAny = foldMap Any . map boolMap]
    putStr "\n"

    putStrLn "Testing prop_universal_property_commuting"
    sequence $ [quickCheck (prop_universal_property_commuting testMap boolListToAny) | boolMap <- allBoolMaps, let testMap = Any . boolMap, let boolListToAny = foldMap Any . map boolMap]
    putStr "\n"
    putStr "\n"
  where allBoolMaps :: [Basis2 -> UnderLyingSetOfAny]
        allBoolMaps = [id, not, const True, const False]


main = do
    maybeBoolList_IsNotFree_Proof1
    maybeBoolList_IsNotFree_Proof2
    boolList_IsFree_For_Any