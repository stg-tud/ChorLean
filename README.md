# ChorLean

Implementation of choreographic library based programming in the style of HasChor/MultiChor

## Usage

### Roles

First, a Choreo requires an instance of the *Role* class.
*Role* specifies how many entities participate in the choreography and gives them unique string identifiers.
These identifiers are used for debugging information, and to select which role to execute when running choreographies on the command line.
Optionally, the *adj* (adjacency) field can specify which roles are allowed to communicate with which other role. 
By default, there are no restrictions on adjacency between roles.

#### Buyer-Seller Roles

Here is an example Role instance taken from the bookseller example:
```lean
instance: Role where
  N := 2
  name | 0 => "buyer" | 1 => "seller"
```

### Executing Endpoint
Choreographic code is always executed by a single role that runs those instructions relevant to them.
This role is an argument for running choreographies, and usually passed by the user when starting the program on the command line.
Programmers do not have direct access to the endpoint, but only through the libraries API.
This role is called *ep* for endpoint.

### Choreo Monad

Choreographies in ChorLean are written in the *Choreo* Monad.
*Choreo* is parameterized by:
- the set of roles that participate in that function (present roles), all other roles will ignore that code. The set is specified as a predicate over roles, where all roles fulfilling that predicate participate 
- Evidence that the endpoint fulfills the predicate

### Main Entrypoint
Chorlean provides a function that automatically generates the main function for you, called *CHOR_ENTRYPOINT*, and a main function is expected to be defined as:
```lean
def main := CHOR_ENTRYPOINT
```
CHOR_ENTRYPOINT lets you run the choreography by running the Lean program and supplying the *Role.name* as the first command line argument.
CHOR_ENTRYPOINT expects an instance of the *ChorMain* class, containing the actual Main method.
The Main method maps the command line inputs as a faceted list of strings, to a choreography that initially contains *all* roles.

### Located Values and Types

Types in ChorLean are annotated by which roles have knowledge of them by predicates (similar to present roles).
They are notated as *α @ p* where *α* is a type and *p* a predicate over roles.
Located values are defined as functions from evidence, that the endpoint has knowledge of the value (fulfills the predicate), to the value itself. Such evidence can be gathered by *enclaving*.
Helpful functions around located values include:

- Located.wrap: wraps values into located values
- Located.flatten: removes one layer of nested located values
- Located.cast: casts into a located value with different predicate *p'*, if *(p x -> p' x)*. This is also helpful when two propositions describe the same set of roles, like *x ∈ [A]* and *x=A*

#### Faceted
Maps roles to located values which are located at them. Helpful for parallel computations.

### Basic Operations

The Core of ChorLean is built on only 3 functions

1. Enclave: embeds a choreography containing less present roles into a bigger one.
2. Broadcast: broadcasts a located value to all present roles, such that it can then be used as a non-located value.
3. Locally: runs a program on the present role. *Requires* a single location to be present.

### Other helpful functions and notations:

#### Enclaves

The examples make use the following notation for enclave: *a ~ b* and *a ° b*, where *a* is something with a membership relation (like lists) and *b* is the subchoreography to enclave. Using the *°*, the result of the enclave is also broadcasted. By *[A]° locally IO.getLine* the Role A would perform a getline program locally and broadcast it afterwards.

#### Parallel

Iterates over all present roles to perform a program locally on them. The program in this case has knowledge of the identity of the executing role. Results in *faceted* values. A Choreography where every role prints their identity looks like this
```lean
par fun id => IO.println s!"hello from {id}"
```

#### Scatter/Gather

A sender can scatter data located at him by sending every present role a value of the same type, resulting in a faceted value. To inverse this, a faceted value can be gathered in a single location again.
Additionally, there is a *scatterList* and *gatherList* variant, which scatters and gathers list items evenly. *gatherAll* is a variant of gather that gathers results replicated at all roles, not just a single one.

## Examples
run the examples by:
```
booseller:
lake exe books buyer
lake exe books seller

authentication:
lake exe auth client
lake exe auth service
lake exe auth IP

mergesort:
lake exe merge master
lake exe merge W1
lake exe merge W2
```