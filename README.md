# userp
This is a tool for formatting Rust code. In particular, it clusters use statements like this:

**BEFORE**:
``` rust
use std::collections::{HashSet, BTreeSet};
use {serde, combine::*};
use itertools::Iterator;
use crate::foo::bar;
use crate::foo::baz;
use crate::badger;
use std::collections::HashMap;
```

**AFTER**:
``` rust
use std::collections::{BTreeSet, HashMap, HashSet};

use {combine::*, itertools::Iterator, serde};

use crate::{badger, foo::{bar, baz}};
```

## How it works
`userp` recursively looks for `.rs` files and does a shallow parse of them, looking specifically for `use` statements. These are grouped and written to the `.rs` file. Then `userp` runs `cargofmt` on them.

`userp` clusters the `use` statements by this order:

* `use std::`
* third party
* workspace members
* `use crate::`
* `use super::`
* `use self::`

Workspace members are found by parsing the root `Cargo.toml`, or can be given with the `--special` flag.
