
odds
====

Odds and ends — collection miscellania.

Please read the `API documentation here`__

__ http://bluss.github.io/arrayvec/doc/odds

|build_status|_ |crates|_

.. |build_status| image:: https://travis-ci.org/bluss/odds.svg
.. _build_status: https://travis-ci.org/bluss/odds

.. |crates| image:: http://meritbadge.herokuapp.com/odds
.. _crates: https://crates.io/crates/odds

Recent Changes
--------------

- 0.2.5
  
  - Add `StringExt::insert_str` and `VecExt::splice`

- 0.2.4

  - Add `odds::string::StrExt`, extensions to `&str`.

- 0.2.3

  - Add default for Fix so that ``Fix<T> == Fix<T, T>``

- 0.2.2

  - Add ptr_eq, ref_eq

- 0.2.1

  - Add slice_unchecked

- 0.2.0

  - Removed **Void**, see ``void`` crate instead.

License
-------

Dual-licensed to be compatible with the Rust project.

Licensed under the Apache License, Version 2.0
http://www.apache.org/licenses/LICENSE-2.0 or the MIT license
http://opensource.org/licenses/MIT, at your
option. This file may not be copied, modified, or distributed
except according to those terms.


