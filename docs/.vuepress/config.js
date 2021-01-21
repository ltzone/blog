module.exports = {
	title: "LTZone",
	description: "Tony's Blog",
	plugins: {
		"vuepress-plugin-auto-sidebar": {
			titleMode: "titlecase",
			titleMap: {
				"CS222": "CS222 Algorithm Analysis",
				"CS258": "CS258 Information Theory",
				"CS263": "CS263 Programming Language",
				"EI332": "EI332 Computer Composition",
				"EI333": "EI333 Software Engineering",
				"EI338": "EI338 System Engineering",
				"EI339": "EI339 Artificial Intelligence",
			}
		}
	},
	head: [
		// ...
		['link', { rel: 'stylesheet', href: "https://cdnjs.cloudflare.com/ajax/libs/KaTeX/0.5.1/katex.min.css" }],
		['link', { rel: "stylesheet", href: "https://cdn.jsdelivr.net/github-markdown-css/2.2.1/github-markdown.css" }]
	],
	markdown: {
		extendMarkdown: md => {
			md.use(require("markdown-it-katex"));
			md.use(require('markdown-it-anchor'));
			md.use(require('markdown-it-table-of-contents'), {
				includeLevel: [2, 3]
			})
		}
	},
	themeConfig: {
		nav: [
			{
				"text": "Course",
				"items": [
					{"text": "CS222 Algorithm Analysis", "link": "/course/CS222/" },
					{"text": "CS258 Information Theory", "link": "/course/CS258/" },
					{"text": "CS263 Programming Language", "link": "/course/CS263/" },
					{"text": "EI332 Computer Composition", "link": "/course/EI332/" },
					{"text": "EI333 Software Engineering", "link": "/course/EI333/" },
					{"text": "EI338 System Engineering", "link": "/course/EI338/" },
					{"text": "EI339 Artificial Intelligence", "link": "/course/EI339/" },
				],
				"link": "/course"
			}]
	}
}