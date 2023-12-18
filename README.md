# FPV Final
## Binary Search Trees

This project includes an implementation of a [binary search tree](https://en.wikipedia.org/wiki/Binary_search_tree) (`BST`), which stores any data associated with a key (as a ℕ).

The structure of a BST dictates that all data stored in the `left` branch has keys less than the root key and the `right` branch similarly has keys greater than the root key. In this implementation, duplicate keys are not allowed.

### Operations
| Name            | Description |
| --------------- | - |
| `insert`        | Adds a key/value pair to a tree at the appropriate location. If the key given already exists in the tree, the old data is overwritten. |
| `get`           | Gets the data associated with the given key. If the key does not exist in the tree, returns `none`. Assumes that the tree has a valid structure. |
| `findMinOrElse` | Finds the minimum value in the tree. If the given tree is just a leaf node, returns a default value. |
| `delete`        | Deletes a node from the tree for a given key. |

### Definitions 
The definitions are descriptors of trees. Their descriptions are in the file. `valid` is particularly important, as it defines the well-formedness of `BST`s
* `inTree`
* `lessThanOrLeaf`
* `greaterThanOrLeaf`
* `valid`

### Proofs
Some of these are unnecessary due to structural changes made, but still hold so I kept them in. Descriptions can be found in the file. 
* `validChildren`
* `inTreeSomewhere`
* `inChildrenInTree`
* `notInChildren`
* `insertValid` (big one!!)
* `insertInTree`
* `insertDeleteEmpty`

I'm running out of time, so some are still `sorry`'d and partially complete. I decided to add `delete` later in the process, so I haven't had a ton of time to thoroughly describe its behavior. Below are the partially complete proofs:
* `deleteValid`
* `insertDelete` (intentionally incomplete)
* `insertDeleteNotIn`

