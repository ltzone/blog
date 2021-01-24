module.exports = {
	title: "LTzone",
	description: "Tony's Blog",
	theme: "reco",
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
			},
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
		type: 'blog',
		authorAvatar: '/id.jpeg',
		nav: [
			{
				text: "Notes",
				items: [
					{ "text": "CS222 Algorithm Analysis", "link": "/course/CS222/" },
					{ "text": "CS258 Information Theory", "link": "/course/CS258/" },
					{ "text": "CS263 Programming Language", "link": "/course/CS263/" },
					{ "text": "EI332 Computer Composition", "link": "/course/EI332/" },
					{ "text": "EI333 Software Engineering", "link": "/course/EI333/" },
					{ "text": "EI338 System Engineering", "link": "/course/EI338/" },
					{ "text": "EI339 Artificial Intelligence", "link": "/course/EI339/" },
				],
				link: "/course/"
			},
			{ text: 'About', line: '/about/'},
			{ text: 'TimeLine', link: '/timeline/', icon: 'reco-date' }
		],
		blogConfig:{
			socialLinks: [     // 信息栏展示社交信息
				{ icon: 'reco-mail', link: "mailto:ltzhou@sjtu.edu.cn"},
				{ icon: 'reco-github', link: 'https://github.com/ltzone' },
				{ icon: 'reco-twitter', link: 'https://twitter.com/tonyzhou0608' }
			  ]
		},
		noFoundPageByTencent: false,
		subSidebar: 'auto',
		author: 'Tony Zhou',
		// 备案
		record: '沪ICP备20004458号',
		recordLink: 'http://www.beian.miit.gov.cn/',
		// 项目开始时间，只填写年份
		startYear: '2020'
	}
}