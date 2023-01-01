# ing-sw-cheatsheet

Cheatsheet per l'esame (open book) di Ingegneria del Software del Politecnico di Milano. A. A. 2022/2023.

## Da dove scaricare il PDF

La versione _nightly_ del PDF è scaricabile al seguente [link](https://github.com/m1gwings/ing-sw-cheatsheet/releases/download/nightly/cheatsheet.pdf).

## Come esportare il PDF

Per poter esportare il PDF è necessario disporre di `node.js` e `git`.

Innanzitutto occorre clonare la repository in locale:
```bash
git clone https://github.com/m1gwings/ing-sw-cheatsheet.git
```

Una volta entrati nella cartella del progetto:
```bash
cd ing-sw-cheatsheet
```
dovremo installare le librerie necessarie allo script in node:
```bash
npm i
```

Siamo pronti per l'esportazione:
```bash
node esporta.js
```

Quando il comando terminerà la sua esecuzione dovrebbe comparire il file `cheatsheet.pdf` all'interno della cartella del progetto.

## Non trovi qualcosa che ritieni utile

Credi che nel cheatsheet manchi qualcosa?

Prima di tutto dai un'occhiata alla lista degli issue aperti, se ciò che manca è riferito ad un capitolo per cui è già presente un issue: puoi aggiungere un commento in quell'issue. Controlla però che l'aggiunta che vuoi richiedere non sia già presente nella task list.
Se invece ciò che manca si riferisce ad un capitolo che non è presente nella lista degli issue, allora puoi aprire un nuovo issue.

## Come contribuire?

Se volete contribuire trovate tutto sul [CONTRIBUTING.md](./CONTRIBUTING.md).
