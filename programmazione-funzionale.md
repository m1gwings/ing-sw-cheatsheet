# Programmazione funzionale

Il paradigma di programmazione funzionale si basa sul principio di considerare le funzioni come oggetti, e quindi utilizzarli come tali. In questo modo, le funzioni possono essere passate come parametri, restituite come risultati, memorizzate in variabili, ecc.
Le funzioni usate come parametro senza specificare il nome della funzione, ma solo il comportamento che essa deve avere, sono dette **funzioni anonime**.

## Espressioni lambda

Supponiamo di avere una classe fatta in questo modo:

```java
class Persona {
    private String nome;
    private int eta;

    public Persona(String nome, int eta) {
        this.nome = nome;
        this.eta = eta;
    }

    public String getNome() {
        return nome;
    }

    public int getEta() {
        return eta;
    }
}
```

e supponiamo di avere una lista di persone: 

```java
List<Persona> persone = new ArrayList<>();
persone.add(new Persona("Mario", 20));
persone.add(new Persona("Luigi", 30));
persone.add(new Persona("Pippo", 40));
persone.add(new Persona("Pluto", 50));
```

Possiamo, ad esempio, ordinare la lista di persone per età, usando il metodo `sort` della classe `Collections`: 
```java
public static <T> void sort(
    List<T> list, Comparator<? super T>
) c
```

Il metodo `sort` prende come primo parametro una lista di oggetti di tipo `T`, e come secondo parametro un oggetto di tipo `Comparator`, possiamo passare un `Comparator` direttamente usando una **espressione lambda**:

```java
obj.method(
    (param1, param2) -> {
        // corpo della funzione
    }
);
```

Nel nostro esempio il metodo `sort` sarà implementato così:

```java
Collections.sort(persone, (p1, p2) -> {
    /* Java conosce già il tipo di p1 e p2, 
    quindi non è necessario specificarlo */
    if(p1.getEta() > p2.getEta()) {
        return 1; }
    else if(p1.getEta() < p2.getEta()) {
        return -1; }
    else return 0;
});
```

## Composizione di funzioni (`Stream<T>`)

Possiamo concatenare delle funzioni che agiscono su una Collezione per costruire una **catena di funzioni**, che filtrerà, mapperà e agirà sulla nostra collezione.

Questa catena inizierà invocando il metodo **`stream()`** sulla collezione. Nell'esempio:

```java
Stream<Persona> stream = persone.stream();
```

### `filter`

Possiamo filtrare lo `stream` per far si che tutti gli elementi della collezione soddisfino un cetro predicato (funzione che restituisce solo true o false).
Per farlo, usiamo il metodo **`Stream<T> filter(<predicato>)`**. Nel nostro esempio, vogliamo filtrare le persone che hanno più di 30 anni:

```java
Stream<Persona> stream = persone.stream()
    .filter(p -> p.getEta() >= 30);
```

La funzione lambda nel metodo `filter` sarà `true` per tre persone: Luigi, Pippo e Pluto. Verrà quindi eliminato Mario (che ha 20 anni) dal nostro `stream`.

### `map`

**`Stream<U> map(<funzione da T a U>)`** prende in input una funzione e la applica ad ogni elemento dello `stream`. Si usa per trasformare gli elementi dello `stream` in altri elementi. Nel nostro esempio, vogliamo trasformare le persone (già filtrate) in stringhe contenenti il nome e l'età:

```java
Stream<String> stream = persone.stream()
    .filter(p -> p.getEta() >= 30)
    .map(p -> {
        return p.getNome() + ": " + 
        p.getEta().toString();
    });
    /* return implicito 
    (valido solo per funzioni 
    con una sola riga) */
```

Otterrò uno `stream`, contenente le stringhe: "Luigi: 30", "Pippo: 40", "Pluto: 50".

### `distinct` e `sort`

- **`Stream<T> distinct()`** elimina gli elementi duplicati dello `stream`.

- **`Stream<T> sort()`** ordina gli elementi dello `stream`. Ha bisogno di un `Comparator` per oggetti diversi da `Integer` e `String`.

---

### `flatMap`

**`Stream<U> flatMap(<funzione da T a Stream<U>>)`** prende in input una funzione, la applica ad ogni elemento di tipo T dello `stream`. La funzione restituisce un altro `stream` (in generale contentente elementi di tipo diverso U) per ogni elemento. Infine tutti gli `stream` restituiti dalla funzione vengono concatenati in un unico `stream`.

Nel nostro esempio, vogliamo trasformare ogni persona (sempre filtrata con età >= 30) in una lista di stringhe contenenti il nome e l'età, e poi concatenare tutti gli `stream` in un unico `stream`:

```java
Stream<String> stream = persone.stream()
    .filter(p -> p.getEta() >= 30)
    .flatMap(p -> {
        List<String> listaPerP;
        listaPerP = new ArrayList<>();
        listaPerP.add(p.getNome());
        listaPerP.add(p.getEta().toString());
        return listaPerP.stream();
    });
```

Otterrò uno `stream`, contenente le stringhe: "Luigi", "30", "Pippo", "40", "Pluto", "50".

### `reduce`

La **`T reduce(Identità, <funzione binaria>)`** è un'operazione di aggregazione che restituisce un singolo valore a partire da uno `stream`. 

Si ha come primo parametro un valore iniziale (identità), e come secondo parametro una funzione binaria che prende in input due elementi dello `stream` e restituisce un altro elemento (dello stesso tipo) ottenuto a partire dai due. La funzione verrà applicata induttivamente ad ogni elemento dello `stream`, fino ad ottenere un solo elemento.

Nel nostro esempio, vogliamo ottenere la somma delle età delle persone (filtrate):

```java
Integer sommaEta = persone.stream()
    .filter(p -> p.getEta() >= 30)
    /* mapToInt è uguale alla map, 
    ma restituisce uno stream di interi */
    .mapToInt(p -> p.getEta())  
    .reduce(
        0, 
        (eta1, eta2) -> eta1 + eta2 );
```

Otterrò un intero: 120. Nelle varie iterazioni nello `stream` contentente le età `[30, 40, 50]`, la `reduce` si applica in questo modo: 

- 0 (valore iniziale) + 30 (primo elemento dello stream) = 30 (risultato parziale), 
- 30 (risultato parziale della iterazione precedente) + 40 (secondo elemento dello stream) = 70, 
- 70 + 50 = 120.

### `collect`

Siamo ora interessati ad avere una Collezione (List, Set, ...) invece che uno stream. Per fare ciò, possiamo usare il metodo **`Collection<T> collect(<funzione che restituisce una Collezione>)`**. Nel nostro esempio, vogliamo ottenere una lista di stringhe contenente nome: età delle persone (filtrate con età >= 30):

```java
List<String> lista = persone.stream()
    .filter(p -> p.getEta() >= 30)
    .map(p -> 
        p.getNome() + ": " + 
        p.getEta().toString()
    );
    .collect(Collectors.toList());
```

### `forEach`

Possiamo usare il metodo **`forEach(<funzione da T a void>)`** per eseguire una funzione per ogni elemento dello stream. Nel nostro esempio, vogliamo stampare il nome e l'età di ogni persona (filtrata con età >= 30):

```java
persone.stream()
    .filter(p -> p.getEta() >= 30)
    .forEach(p -> 
        System.out.println(p.getNome() + ": "
        + p.getEta().toString()));
```

## `Optional<T>`

L'oggetto **`Optional`** è un contenitore per un valore che può essere nullo. È usato per evitare di avere eccezioni di tipo `NullPointerException`.

Possiamo creare un `Optional` con il valore `val` con il metodo `Optional.of(val)`. Oppure con il metodo `Optional.empty()` per creare un `Optional` vuoto (sostituisce il null).

Sono poi disponibili i metodi per lavorare con gli Optional:

- **`ifPresent(<funzione>)`** che applica la funzione in input solo se l'Optional non è vuoto.

- **`orElse(<val>)`** che restituisce il valore dell'Optional se non è vuoto, altrimenti restituisce il valore `val` in input.

- **`flatMap(<funzione da T a Optional<U>)`** restituisce un `Optional<U>`, applicando la funzione in input solo se l'`Optional` non è vuoto.

---

Facciamo un esempio usando gli `Optional` e i tre metodi visti in precendenza:

```java
Optional<String> opt = Optional.of("ciao");

// Stampa "ciao"
opt.ifPresent(s -> System.out.println(s));

// Stampa "ciao" perché opt non è vuoto
System.out.println(opt.orElse("vuoto"));

/* La funzione in flatMap viene applicata
e restituisce un Optional<String> 
contenente "ciao mondo", 
quindi viene stampato "ciao mondo" 
per effetto della orElse */
System.out.println(
    opt .flatMap(
        s -> Optional.of(s + " mondo"))
    .orElse("vuoto"));


Optional<String> opt2 = Optional.empty();

// Non stampa nulla perché opt2 è vuoto
opt2.ifPresent(s -> System.out.println(s));

// Stampa "vuoto" perché opt2 è vuoto
System.out.println(opt2.orElse("vuoto"));

/* La funzione in flatMap non viene applicata
e restituisce un Optional<String> vuoto, 
quindi viene stampato "vuoto" 
per effetto della orElse */
System.out.println(
    opt2.flatMap(
        s -> Optional.of(s + " mondo"))
    .orElse("vuoto"));
```

Otterremo in output:
```
    ciao
    ciao
    ciao mondo
    vuoto
    vuoto
```
