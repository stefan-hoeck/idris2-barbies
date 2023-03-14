# Barbies: Types that can change their clothes

When working with regular (that is: non-dependent) data types
for representing an application's domain model, it can be useful
to parameterise these types by a function of type `Type -> Type`,
or even `k -> Type`.

```idris
import Control.Barbie
import Derive.Barbie
import Derive.Prelude

%default total
%language ElabReflection
```

<!-- vi: filetype=idris2:syntax=markdown
-->

