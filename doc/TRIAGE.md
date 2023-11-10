# Triage

## Preface

This document elaborates on the triage process that we use to prioritize and resolve incoming requests, bug reports, questions -- anything relevant to the contents of this repo that the reporter wants to bring to our attention. The goal is to make sure that every issue or pull request opened on GitHub gets evaluated, classified, put into the queue and eventually resolved.

## Why

Before we start, why even bother with triage? It's another thing to learn and spend time on, why do we consider this a worthwhile effort investment? Here are a couple of reasons:

- We care about our users. There isn't much point in developing something and then ignoring the feedback of people for whom you developed the product in the first place. Satisfaction of our users is the most important indicator that we do well, hence we always need to keep user experience in mind and work towards improving it, as otherwise people will go elsewhere.
- There have been numerous times that our users not only reported important findings, but also fully investigated a potential issue and proposed a reasonable way forward (check out [#5135](https://github.com/input-output-hk/plutus/issues/5135) and [#5185](https://github.com/input-output-hk/plutus/issues/5185) for a couple of great examples). We don't want to miss out on those by not handling reported issues properly.

As for why we need a process -- it's simple: because otherwise we'd revert back to shortly glossing over an issue and moving on hoping it'll somehow resolve itself. This strategy wasn't working well and we would easily forget about an important report or even miss it completely in the past, hence we decided to create a dedicated process.

Now that there's a dedicated process, we encourage the community to report issues on GitHub, so that we can tackle them efficiently. This doesn't mean that an issue reported elsewhere is going to be ignored -- it's a responsibility of any Plutus team member to escalate a potentially important issue regardless of where it was reported, however it can be much harder to recognize such a report upon accidentally encountering it on a public forum or some other random place. In contrast, reporting an issue on GitHub guarantees that the Plutus team will look into it.

Triaging is generally expected to affect the scope of work being done by the Plutus team, both long-term and short-term whenever appropriate (for example, a reported vulnerability needs to be investigated as soon as possible and, if confirmed, fixing it needs to be put at the top of the development queue immediately).

## Metacommentary

The content of a directly harmful issue/comment (spam, phishing, any kinds of malware, violent threats, extremely offensive language etc) needs to be copied and reported to the team privately with the original issue/comment deleted. It is a responsibility of every team member to perform these actions upon encountering such content.

Anybody feeling that they can contribute to a discussion in a GitHub issue or anywhere else, are encouraged to do so without feeling obligated to follow any specific process as long as the contribution doesn't violate our [code of conduct](https://github.com/input-output-hk/cardano-engineering-handbook/blob/d3ce5a2276a0176fc542fe157b1758f11691a636/CODE-OF-CONDUCT.md), of course.

The triage role is only available for members of the Plutus team as the whole point of the process is to make sure that information reaches the right members of the Plutus team and issues get prioritized properly.

Any member of the Plutus team can triage any issue at any time if they feel so. It is expected however that in most cases issues are going to get triaged by a person serving the triage role, which is a responsibility that is cycled through all members of the Plutus team.

One reason why the role is cycled is that in addition to being generally helpful triaging is a natural way to get exposure to parts of the project that one is not directly involved with, which promotes collaboration, improves the quality of the product and reduces the [bus factor](https://en.wikipedia.org/wiki/Bus_factor).

If the person serving the triage role reaches out to you, please provide all the help that they need. Everyone is generally expected to be helpful to teammates, however when it comes to triage specifically, since the role is cycled, you'll soon be at the other side of the table and it's in your best interest to lead by example.

## Triage in general

The process described in this section and every section below is intended for the person serving the triage role (whether voluntarily or by duty). The process is meant to provide guidance and outline best practices -- not prescribe any rigid patterns that must be followed meticulously. Always use your best judgement and if something reasonable doesn't fit the process, consider amending the process.

Remember to be nice and helpful to people you interact with: answer questions, provide additional context, explain why things are the way they are and how and why we are going (not) to change them with regards to the given issue.

In a lot of cases the participants are going to be disappointed with our product, since a place for reporting issues naturally skews towards negative feedback, and that disappointment may be very visible. Don't take it personally, chances are, there's indeed an annoying technical issue and the reporter has been struggling with it for a while before deciding to report it, which isn't a particularly entertaining thing to do either. Reporting issues can generally be a draining and thankless process and we don't want to hold up to this expectation. We want people reporting issues to feel welcome, even if they eagerly criticize our work.

However if you don't feel comfortable triaging a certain issue (for any reason, including but not limited to someone in the issue thread being more hostile than you can easily tolerate), do feel free to inform the team of that and we'll figure out whether to assign the issue to a different person or to handle it in some other way.

When serving the triage role, your main responsibility is to move a number of issues forward. We do not mandate any specific number of issues to tackle or any specific amount of time to devote to triaging issues, but here are some general guidelines:

- Try to triage every issue that was created during the time you've been serving the triage role. If it's hard to keep up with everything, reach out to the team and ask for help -- we want to make sure that issues get triaged speedily.
- Try to resolve at least one old issue per week. Failing that, make sure to at least move forward a few old ones.

### Closing issues

The best thing you can do with an issue is close it with a reasonable explanation. Here are some examples of when it makes sense to close an issue:

- The issue was resolved (the bug was fixed, the requested functionality was implemented, the question was answered etc).
- The issue is out of scope of the project. For example, we can't introduce non-determinism into Plutus scripts, so any issue with a request such as "consider adding random number generation to Plutus" can be closed right away.
- The issue does not reproduce and the reporter does not fulfill a request for additional information. For example, we can't do much about "build fails on my machine" with no additional context.
- It was decided by the team that the reported bug is a feature or the requested changes aren't an improvement over the status quo.
- Too radical changes are requested, but even some of the clearly beneficial ones aren't viewed by the team as cost-effective. But don't just close an issue because it's low-priority -- only if it's both enormous and a very low-priority one.
- The issue is a duplicate of another one. When closing, make sure to provide a link to the existing issue. If the duplicate has additional information that the original issue doesn't have, then copy-paste the information into the original issue (credit the reporter properly, of course). In general, if one issue/PR is related to another PR/issue, establish the relation between them in a comment. If there's any internal ticket associated with an issue/PR, link it as well just for us to keep track.

Don't keep issues that are not going to be worked on open.

If you're closing an issue, make it clear why. Even if it's obvious to you why the issue is getting closed, it may not be as obvious to the participants. In general, explain your actions in the issue, particularly if you're closing the issue as "won't do" or labeling it as a low-priority one or doing anything else that may disappoint the participants. Encourage the participants to express their disagreement. For example if you're closing an issue, especially with a reason other than "resolved in this PR" (with a link to the PR), make it clear that if somebody disagrees with the decision to close the issue, they are encouraged to reopen it.

### Moving issues forward

The next best thing that you can do is move the issue forward in some way. If there hasn't been any progress on an issue for a while, a reasonable question to ask is "why?", for example:

- Is it because nobody has been looking at it for a while?
- Or is it unclear what the scope of the issue is?
- Or is it complicated and nobody performed a deep dive?
- Or is it controversial?
- Or is it considered low-priority?

Depending on the reason why the question has been stuck, your actions can be:

- Ping the right person.
- Request additional information.
- Look into the issue yourself.
- Escalate the issue to the team.
- Ask the participants to help with moving the issue forward, e.g. by creating a PR resolving it.

Regarding the last one: it is fine to ask the reporter or anybody from the community to help with an issue. Just keep in mind that you're asking for help, accept a "no" and be explicitly grateful if any help is provided, even if it's not very much. Never ever make it seem like somebody who wasn't paid for the specific work by IOG or one of its subsidiaries is expected to perform said work.

### Pinging people

Pinging people is something that you're going to do a lot while serving the triage role, so we'll discuss it in detail.

You can ping people privately via DMs or in public Slack channels or directly on GitHub -- as you see fit.

Don't ping a lot of people at the same time, 1-2 should be enough in most cases, unless you're escalating an issue to the entire team on Slack.

In general, try to pick the person who has the most knowledge about the given topic. However factor in any additional information that you have, for example if you know that somebody is on leave, ping your next best pick instead. Similarly, ping next best pick if you find yourself pinging the same person over and over again with regards to different issues. But if you do need to ping somebody ten times in a short period of time, do that, just keep in mind that you probably won't get ten elaborated answers in a row.

If you read the description of an issue and don't even understand the terminology used, but know who on the team understands it, it is fine to ping that person right away. It is also fine to take time and get familiar with the terminology used, so use your judgement. If you have no idea whom to ping, ask the team on Slack.

It is fine to immediately ping somebody if you suspect they might know the answer to the question asked right away.

To be very clear, you're not expected to resolve any issue yourself by implementing a fix for example. However if you feel like there's a chance that it won't take long to resolve an issue, do try to do it yourself right away. But if you're not making progress within 30 minutes to an hour, ask somebody.

Triaging isn't meant to compete with the regular planning process, so don't do any sizeable amount of work without this work going through proper prioritization as per our development routine.

### Ownership

Just pinging somebody isn't making progress. Make sure the person you've pinged responds and do feel free to bug them until they do. Once a week or two weeks should be reasonable for issues that are not high-priority. For high-priority ones raise the issue as soon as possible on Slack to the whole team and do it vocally.

In general, once you've triaged an issue it becomes your responsibility to follow up on it, which includes not only pinging people, but also making sure that the work on the issue is being planned, put into a sprint and eventually actually performed. It is exclusively your responsibility to make sure that an issue triaged by you is tracked and that progress is more or less regularly made. This is irrespective of whether another person has taken on the triage role. Once you triage an issue, it's yours until some other person takes over it, which needs to be explicitly reflected in the issue thread.

Every issue labeled as "status: needs action from the team" (more on that later) needs to have the "assignee" field filled with the name of the person who triaged the issue, so once you've triaged an issue, please fill the field with your name. You cannot fill the field with other's person name. This is because we want to ensure that people are fully aware of their responsibilities, as otherwise it's trivial to forget about an issue: one person triages it, assigns it to another person and feels like their job is done, while the other person isn't even aware that there's an issue assigned to them. People are also more keen to serve a duty that they've taken on themselves as opposed to being randomly assigned by somebody else.

Note how issues are not assigned to those who are supposed to resolve them by submitting PRs for example. This is because for that we have our regular development process with sprints and tickets and whatnot, so there wouldn't be much sense in duplicating this information on GitHub.

Do feel free to assign any issue to yourself if you want to track it and follow up on it.

### Labeling

We use the GitHub labels feature. Reasons:

- For our own sake: a status label is easily accessible and makes it clear what the status of each issue is and whether it requires attention or not. You can even use labels in filter queries and specifically look for issues that may require attention (more on that below). Every single issue must have a `status: <something>` label.
- For the sake of our users: a label succinctly summarizes how the team views the issue and whether to expect any action on it in the foreseeable future or not.

There's no obligation to polish labels on an issue that you're about to close. In general, don't worry about labels on closed issues. However if an issue got reopened, then you do need to label it appropriately.

Below you'll find the full list of "regulated" labels. If you introduce a new such label, please add it to the list. All other labels (e.g. `enhancement`, `Performance`, `Refactoring` etc) can be used freely, i.e. feel free to use or not to use any of them (and if any such label was added by a user, then only remove it if it's wrong as we don't want to discourage engagement).

The list of regulated labels:

- `status: needs triage` -- means that the issue hasn't been triaged yet and requires attention. Note that any amount of discussion isn't indicative of the issue being successfully triaged. I.e. as long as this label is there, the issue still requires attention. Once the issue is triaged, this label must be replaced with some other `status: <something>` one. This label is added automatically to every new issue.
- `status: needs action from the team` -- means that the issue needs to be addressed by the team. Not necessarily ASAP, but better sooner than later, depending on what is determined during the prioritization process. In any case such an issue needs to be actively tracked and progress must be regularly reported in the issue (once any substantial progress is made or every month or two otherwise). It is fine to demote the issue in future and label it differently, if it's what the team arrives at during the prioritization process.
- `status: needs info from the reporter` -- means that the issue is _blocked_ by means of us not having some information that we need. Don't use this label if you just asked a clarifying question and aren't blocked by not having an answer. In general, if progress can be made on the issue and having additional information wouldn't speed that up considerably, then this label shouldn't be used. Change the label once the required information is provided.
- `status: triaged` -- means that the issue has been triaged and deemed reasonable but not requiring immediate attention. The reason why the issue doesn't require immediate attention must be reflected in another label, of which we only have:
  - `Low priority` -- self-explanatory, but do write a comment making it clear why the issue is considered low-priority. It is fine to use this label with issues not labeled as `status: triaged`.
  - `Internal` -- an employee of IOG or one of its subsidiaries has opened the issue and is working or going to work on it. We don't need to provide a lot of feedback to ourselves via GitHub issues, so internal issues aren't regulated as much.
  - `Objective` -- there's a certain class of issues that can neither be closed nor fully resolved. For example, someone reports that evaluation is slow and we need to work on speeding it up. Neither does it make sense to close such an issue (especially when it has concrete suggestions), nor can we speed up evaluation a bit and resolve the issue on this basis. What we can do here is tell the reporter that we recognize the problem and have a dedicated objective to work on improving the situation. However before using such a label, make sure that the objective does actually exist and there's a plan in place on improving the situation (not necessarily resolving it fully). Use this label sparingly and only for issues that are indeed open-ended objectives and not specific requests (even if such a request falls under a certain objective).
- `bug` -- means that we recognize that the reported behavior is wrong and we have an intention to fix it. Issues labeled this way tend to be high-priority, however if the bug is in a not too important test for example, then there is nothing high-priority about it and the issue can wait, i.e. in principle it is fine to mix `bug` with `Low priority` for example.

### Useful queries

Issues assigned to you sorted by update date with the ones that haven't been updated in a while appearing first:

```
is:issue is:open assignee:@me sort:updated-asc
```

Issues that don't have an assignee and may require attention:

```
is:issue is:open no:assignee -label:"Internal" -label:"Low priority" -label:"status: needs info from the reporter"
```
