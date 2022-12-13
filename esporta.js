import { Marpit } from '@marp-team/marpit'
import markdownItContainer from 'markdown-it-container'
import markdownItMermaid from 'markdown-it-mermaid-plugin'
import fs from 'fs'
import express from 'express'
import puppeteer from 'puppeteer'

const percorsoFileIndice = 'indice.json'
const percorsoFileStile = 'stile.css'
const percorsoFileHTML = 'cheatsheet.html'
const percorsoFileOutput = 'cheatsheet.pdf'

const numeroPorta = 8080

const marpit = new Marpit().use(markdownItContainer, 'columns')
    .use(markdownItMermaid)

const tema = fs.readFileSync(percorsoFileStile, 'utf-8')
marpit.themeSet.default = marpit.themeSet.add(tema)

const temaMermaid = `%%{init: {'theme': 'base', 'themeVariables': { 'primaryColor': '#FFFFFF',
    'primaryBorderColor': '#000000'}}}%%`

let markdown = `---

marp: true
paginate: true

---

# Cheatsheet di Ingegneria del Software A.A. 2022/2023

## Indice

`

const indiceJSON = fs.readFileSync(percorsoFileIndice, 'utf-8')
const indice = JSON.parse(indiceJSON)

for (let i = 0; i < indice.capitoli.length; i++) {
    let nomeCapitolo = indice.capitoli[i].nome
    markdown += '- ' + nomeCapitolo + '\n'
}
markdown += '\n'

for (let i = 0; i < indice.capitoli.length; i++) {
    const percorsoFileCapitolo = indice.capitoli[i].file + '.md'
    let markdownCapitolo = fs.readFileSync(percorsoFileCapitolo, 'utf-8')

    // Aggiunge il tema custom ad ogni diagramma di mermaid
    markdownCapitolo = markdownCapitolo.replaceAll('```mermaid\n', '```mermaid\n' + temaMermaid + '\n')
    markdown += markdownCapitolo + ((i < indice.capitoli.length - 1) ? '\n---\n' : '')
}

const { html, css } = marpit.render(markdown)

const fileHTML = `
<!DOCTYPE html>
<head>
    <style>
        .marpit {
            width: fit-content;
            height: fit-content;
        }
    </style>
</head>
<html style="margin: 0mm; padding: 0mm; height: fit-content; width: fit-content;">
    <body style="margin: 0mm; padding: 0mm; height: fit-content; width: fit-content;">
        <script type="module">
            import mermaid from './mermaid/mermaid.esm.min.js';
            mermaid.initialize({ theme: 'base', startOnLoad: true });
        </script>
        <style>${css}</style>
        ${html}
    </body>
</html>
`

fs.writeFileSync(percorsoFileHTML, fileHTML)

const app = express();
app.use(express.static('./'))

const server = app.listen(numeroPorta, () => {
    puppeteer.launch().then(browser => {
        browser.newPage().then(pagina => {
            pagina.goto(`http://localhost:${numeroPorta}/${percorsoFileHTML}`, { waitUntil: 'networkidle0' }).then(() => {
                pagina.emulateMediaType('screen').then(() => {
                    pagina.pdf({
                        path: percorsoFileOutput,
                        format: 'A4',
                        landscape: true,
                        printBackground: true
                    }).then(pdf => {
                        browser.close().then(() =>
                            server.close()
                        )
                    })
                })
            })
        })
    })
})
