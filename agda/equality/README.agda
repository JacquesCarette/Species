------------------------------------------------------------------------
-- Experiments related to equality
--
-- Nils Anders Danielsson
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module README where

-- Definitions of some basic types and some related functions.

import Prelude

-- Logical equivalences.

import Logical-equivalence

-- Two logically equivalent axiomatisations of equality. Many of the
-- modules below are parametrised by a definition of equality that
-- satisfies these axioms. The reason for this parametrisation is that
-- I might later want to use a definition of equality where the
-- application elim P r (refl x) does not compute to r x, unlike the
-- equality in Equality.Propositional. (Equality.Tactic also contains
-- a definition of equality which, roughly speaking, computes in this
-- way.)

import Equality

-- One model of the axioms: propositional equality.

import Equality.Propositional

-- A simple tactic for proving equality of equality proofs (at the
-- time of writing only used in Equality.Groupoid).

import Equality.Tactic

-- Some decision procedures for equality.

import Equality.Decision-procedures

-- A proof which shows that sets with decidable equality have unique
-- identity proofs.

import Equality.Decidable-UIP

-- Groupoids.

import Groupoid

-- Equalities can be turned into groupoids which are sometimes
-- commutative.

import Equality.Groupoid

-- Injections.

import Injection

-- Split surjections.

import Surjection

-- Bijections.

import Bijection

-- All instances of the equality axioms are isomorphic.

import Equality.Instances-isomorphic

-- H-levels, along with some general properties.

import H-level

-- Closure properties for h-levels.

import H-level.Closure

-- Preimages.

import Preimage

-- Equivalences.

import Equivalence

-- A universe which includes several kinds of functions (ordinary
-- functions, logical equivalences, injections, surjections,
-- bijections and equivalences).

import Function-universe

-- The univalence axiom.

import Univalence-axiom

-- Isomorphism of monoids on sets coincides with equality (assuming
-- univalence).

import Univalence-axiom.Isomorphism-is-equality.Monoid

-- In fact, several large classes of algebraic structures satisfy the
-- property that isomorphism coincides with equality (assuming
-- univalence).

import Univalence-axiom.Isomorphism-is-equality.Simple
import Univalence-axiom.Isomorphism-is-equality.Simple.Variant
import Univalence-axiom.Isomorphism-is-equality.More
import Univalence-axiom.Isomorphism-is-equality.More.Examples

-- A class of structures that satisfies the property that isomorphic
-- instances of a structure are equal (assuming univalence). This code
-- is superseded by the code above, but preserved because it is
-- mentioned in a blog post.

import Univalence-axiom.Isomorphism-implies-equality

-- 1-categories.

import Category

-- Aczel's structure identity principle (for 1-categories).

import Structure-identity-principle

-- M-types.

import M

-- Some definitions related to and properties of finite sets.

import Fin

-- Bag equivalence for lists.

import Bag-equivalence

-- Implementations of tree sort. One only establishes that the
-- algorithm permutes its input, the other one also establishes
-- sortedness.

import Tree-sort.Partial
import Tree-sort.Full
import Tree-sort.Examples

-- Containers, including a definition of bag equivalence.

import Container

-- An implementation of tree sort which uses containers to represent
-- trees and lists.
--
-- In the module Tree-sort.Full indexed types are used to enforce
-- sortedness, but Containers contains a definition of non-indexed
-- containers, so sortedness is not enforced in this development.
--
-- The implementation using containers has the advantage of uniform
-- definitions of Any/membership/bag equivalence, but the other
-- implementations use more direct definitions and are perhaps a bit
-- "leaner".

import Container.List
import Container.Tree
import Container.Tree-sort
import Container.Tree-sort.Example

-- The stream container.

import Container.Stream

-- Overview of code related to some papers.

import README.Bag-equivalence
import README.Isomorphism-is-equality
