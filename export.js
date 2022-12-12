import { Marpit } from '@marp-team/marpit'
import markdownItContainer from 'markdown-it-container'
import fs from 'fs'
import express from 'express'
import puppeteer from 'puppeteer'

const percorsoFileIndice = 'indice.json'
const percorsoFileStile = 'style.css'
const percorsoFileHTML = 'cheatsheet.html'
const percorsoFileOutput = 'cheatsheet.pdf'

const numeroPorta = 8080

const marpit = new Marpit().use(markdownItContainer, 'columns')

const tema = fs.readFileSync(percorsoFileStile, 'utf-8')
marpit.themeSet.default = marpit.themeSet.add(tema)

let markdown = `---

marp: true
paginate: true

---

# Cheatsheet di Ingegneria del Software A.A. 2022/2023

## Indice

`

const indiceJSON = fs.readFileSync(percorsoFileIndice, 'utf-8')
const indice = JSON.parse(indiceJSON)

function formattaCapitolo(capitolo) {
    let capitoloFormattato = capitolo.charAt(0).toUpperCase()
    for (let i = 1; i < capitolo.length; i++) {
        capitoloFormattato += ((capitolo.charAt(i) == '-') ? ' ' : capitolo.charAt(i))
    }
    return capitoloFormattato
}

for (let i = 0; i < indice.capitoli.length; i++) {
    let capitolo = indice.capitoli[i]
    markdown += '- ' + formattaCapitolo(capitolo) + '\n'
}
markdown += '\n'

for (let i = 0; i < indice.capitoli.length; i++) {
    let capitolo = indice.capitoli[i]
    const markdownCapitolo = fs.readFileSync(capitolo + '.md', 'utf-8')
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
