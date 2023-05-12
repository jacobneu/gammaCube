![The Gamma Cube Agda Formalization banner](/misc/banner.png?raw=true "The Gamma Cube - Agda Formalization")

## What is the $\Gamma$-Cube?

The $\Gamma$-cube consists of eight categories of structures, each of which can serve as the underlying category for a model of dependent type theory. These eight models include some of the most important interpretations of type theory in the literature, and serve as a standard point of reference for semantic investigations.

![The axes of the Gamma cube](/misc/axes.png?raw=true "The Gamma Cube - axes")
The three axes for defining the cube are **dimension**, **univalence**, and **polarity**.

- The genesis of the _groupoid model of type theory_ was the famous proof by Hofmann and Streicher that the _uniqueness of identity proofs_ principle was independent of the usual rules of Martin-Löf Type Theory. To prove this, they had to establish a countermodel which had identity types with multiple, distinct elements (the groupoid model is such a countermodel). The field of Homotopy Type Theory later clarified this as a kind of '**dimension**', the _truncation level_. The structures on the left face of the $\Gamma$-cube are kinds of sets, i.e. structures with truncation level zero. The right face—including the groupoid model—are structures with truncation level one. In principle, the cube could be extended further along this dimension, e.g. to 2-groupoids.
- The structures on the top face of the $\Gamma$-cube satisfy an appropriate principle of **univalence** or _antisymmetry_. A set is just an antisymmetric setoid, a poset is an antisymmetric preorder, a univalent category is a category satisfying univalence, and so on.
- The structures on the back face of the $\Gamma$-cube serve as models of **polarized** and _directed_ type theory, where covariance and contravariance are explicitly represented in the type theory, and where the symmetric identity types of the front face are replaced by asymmetric "hom-types". The precise nature and properties of polarized and directed type theory is a topic of active research.


## The formalization project

The primary goal of this project is to formalize these different models of type theory, an particularly to study the not-yet-well-understood nature of polarized type theory. A secondary goal, once the different models have been adequately formalized, is to formalized their interrelationships and try to abstract the general theory of this interesting class of models.

Work on this formalization is currently being done by [Jacob Neumann](https://jacobneu.github.io). The formalization of the setoid model comes from [this Agda formalization](https://bitbucket.org/taltenkirch/setoid-univ) by Thorsten Altenkirch, Simon Boulier, Ambrus Kaposi, and Filippo Sestini.
