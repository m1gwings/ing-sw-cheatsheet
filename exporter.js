import { Marpit } from '@marp-team/marpit'
import markdownItContainer from 'markdown-it-container'
import fs from 'fs'
import * as puppeteer from "puppeteer";

const percorsoFileIndice = 'indice.json'
const percorsoFileStile = 'stile.css'
const percorsoFileHTML = 'cheatsheet.html'
const percorsoFileOutput = 'cheatsheet.pdf'

const marpit = new Marpit().use(markdownItContainer, 'columns')
const markdownHeader = `---

marp: true
paginate: true

---

# Cheatsheet di Ingegneria del Software A.A. 2022/2023

## Indice

`

const htmlTemplate = (html, css) => {
    return `
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
};

/** @param {puppeteer.Browser} browser */
export default async (baseUrl, browser) => {
    // Set theme
    marpit.themeSet.default = marpit.themeSet.add(await new Promise((resolve, reject) =>
        fs.readFile(percorsoFileStile, 'utf-8', (err, data) => {
            if (err)
                return reject(err);
            resolve(data);
        })));
    // Build markdown
    const indice = JSON.parse(await new Promise((resolve, reject) =>
        fs.readFile(percorsoFileIndice, 'utf-8', (err, data) => {
            if (err)
                return reject(err);
            resolve(data);
        })));
    const markdown =
        markdownHeader +
        [...indice.capitoli]
            .map(capitolo => capitolo.nome)
            .map(nomeCapitolo => '- ' + nomeCapitolo)
            .join('\n') +
        (await Promise.all([...indice.capitoli]
            .map(capitolo => capitolo.file + '.md')
            .map(pathCapitolo => new Promise((resolve, reject) =>
                fs.readFile(pathCapitolo, 'utf-8', (err, data) => {
                    if (err)
                        return reject(err);
                    resolve(data);
                })))
        )).join('\n\n---\n\n');
    // Render markdown
    const { html, css } = marpit.render(markdown)
    // Build html file
    const fileHTML = htmlTemplate(html, css);
    await new Promise((resolve, reject) => fs.writeFile(percorsoFileHTML, fileHTML, (err) => {
        if (err)
            return reject(err);
        resolve();
    }));

    // Print to PDF
    const pagina = await browser.newPage();
    await pagina.goto(baseUrl + percorsoFileHTML, { waitUntil: 'networkidle0' });
    await pagina.emulateMediaType('screen');
    await pagina.pdf({
        path: percorsoFileOutput,
        format: 'A4',
        landscape: true,
        printBackground: true
    });
};