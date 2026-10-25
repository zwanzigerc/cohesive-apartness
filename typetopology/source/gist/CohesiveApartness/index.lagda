Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 25 October 2026.

AI disclosure. The Agda code, the prose and the mathematical
arguments in this folder are by Claude Opus 5.5, an AI model made by
Anthropic, prompted by Colin Zwanziger in a conversation on 24 and 25
October 2026. The files were type-checked with Agda 2.8.0 against
TypeTopology commit 52ed2eb of 24 October 2026. TypeTopology's
AI-Policy.md says that AI generated Agda code or prose will not be
considered. This folder is therefore offered for discussion only,
unless the maintainers decide otherwise.

Acknowledgement. We thank GPT-6 Astra for reviewing the
formalization.

This folder studies the first two open problems listed in the section
"In cohesive homotopy type theory" of the nLab page

 https://ncatlab.org/nlab/show/open+problems+in+homotopy+type+theory

which concern tight apartness relations in the presence of the flat
modality ♭. See gist.CohesiveApartness.TightApartness for the
statements of the problems, how we read them, and a summary of the
results.

 * gist.CohesiveApartness.Flat defines ♭, ♭-discreteness, crisp
   excluded middle, Shulman's Axioms C0 and C1, and the nLab's
   single-generator variant of Axiom C1, which we call singly
   generated punctual cohesion.

 * gist.CohesiveApartness.TightApartness formulates the two problems
   and shows that, over crisp excluded middle, each is equivalent to
   excluded middle. Under Shulman's Axiom C1, each is equivalent to
   every generator being 0-connected, and under singly generated
   punctual cohesion to the generator being 0-connected. Both
   statements are refuted by Shulman's Axiom C2.

The problems were posed by the nLab contributor Anonymouse, using the
nLab's definition of axiom C1, so technically they refer to singly
generated punctual cohesion. We take Shulman's paper as the authority
on Axiom C1, and give the main results for both definitions.

The modules here use Agda's flag --cohesion, which provides the flat
modality and crisp variables. Because --cohesion is infective, every
module that imports them must use it too, and so must this index
file. The library file typetopology.agda-lib sets --no-cohesion, and
gist.index doesn't use --cohesion. This folder is therefore not
imported by gist.index for the moment. How to handle this, if at all,
is a question for the maintainers.

\begin{code}

{-# OPTIONS --safe --without-K --cohesion #-}

module gist.CohesiveApartness.index where

import gist.CohesiveApartness.Flat
import gist.CohesiveApartness.TightApartness

\end{code}
