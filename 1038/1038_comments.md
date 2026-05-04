Logo
Forum
Inbox
Favourites
Tags
More
  Go
  Go
Dual View
Random Solved
Random Open
OPEN

Determine the infimum and supremum of
|{x∈ℝ:|f(x)|<1}|
as f∈ℝ[x] ranges over all non-constant monic polynomials, all of whose roots are real and in the interval [−1,1].
#1038: [EHP58,p.131]analysis
The open status of this problem reflects the current belief of the owner of this website. There may be literature on this problem that I am unaware of, which may partially or completely solve the stated problem. Please do your own literature search before expending significant effort on solving this problem. If you find any relevant literature not mentioned here, please add this in a comment.
Comment activity that has not yet been incorporated into the remarks

None

Partial

Solution
There are no solutions, partial or complete, claimed in the comments.
A problem of Erdős, Herzog, and Piranian [EHP58], who proved that the measure of the set in question is always at most 22‾√ under the assumption that all the roots are in {−1,1}, and conjecture this is the best possible upper bound.

They also note that the infimum of the set in question is less than 2, as witnessed by f(x)=(x+1)(x−1)m for m≥3. They further note that if the roots are restricted to [−2,2] then the infimum is zero, as witnessed by a small perturbation of the Chebyshev polynomials.

They further conjectured that, if the roots are restricted to [−2,2], then
|{x∈ℝ:|f(x)|<1}|≥n−c
for an absolute constant c>0. This was proved by Pommerenke [Po61], who in fact showed that this set must contain an interval of width ≫n−4.

The current best known bounds (see the discussion in the comments) are
1.519≈24/3−1≤inf≤1.835⋯
and
sup=22‾√≈2.828.
View the LaTeX source

This page was last edited 11 January 2026. View history

External data from the database - you can help update this
Formalised statement? Yes
134 comments on this problem
Likes this problem	TerenceTao, zach_hunter, naprienko (yes)
Interested in collaborating	TerenceTao (yes)
Currently working on this problem	naprienko (yes)
This problem looks difficult	None (yes)
This problem looks tractable	BorisAlexeev, TerenceTao, naprienko, MalekZ (yes)
The results on this problem could be formalisable	None (yes)
I am working on formalising the results on this problem	None (yes)

Additional thanks to: Koizumi, Yongxi Lin, natso26, and Terence Tao

When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is:

T. F. Bloom, Erdős Problem #1038, https://www.erdosproblems.com/1038, accessed 2026-05-01
Order by oldest first or newest first. (The most recent comments are highlighted in a red border.)
GPT-5.4 Thinking has written up and completed some material in this thread for the inf problem in these progress notes.

Summary of material:

- Tao's notes prove some results for a minimizer μ with a convenient assumption of minimal variance. It turns out this assumption can be removed. So for a minimizer μ, it must be a point mass in each interval of Eμ:={Uμ>0}. Moreover, up to reflection and translation, μ({−1})≥1/2 and supp μ⊆{−1}∪[0,1].

- Under some regularity assumptions on μ, first variation is worked out. Let
λ∂:=∑a∈bd Eμ1|U′μ(a)|δa,Z0:={Uμ=0}∖bd Eμ.

Then there is c≥0 and measure ξ supported on Z0, not both zero, such that
λ:=cλ∂+ξ

satisfies: 1) Uλ≥0 in [−1,1]∖{Uμ=0} and Lebesgue-a.e.; 2) Uλ=0 μ-a.e.

- We do calculations related to the ansatz we're doing in the thread, recovering the description of the conjectured minimizer. We also record an alternative transport viewpoint using pushforward measure that potentially does similar things.
natso26
—
17:10 on 19 Mar 2026
| Reply

👍
0

📝
0

🤖
0
I am curious: what is the latest status for this conjecture?

That is, what are the best known bounds, what is expected to be true, and what is still missing?
DustinMixon
—
19:46 on 07 Mar 2026
| Reply

👍
1

📝
0

🤖
0
The current commentary accurately records what we actually know for sure: the sup is known to be exactly 22‾√, and the inf is between 1.519 and 1.835; these notes basically contain these results. The upper bound is likely to be sharp, but we do not yet have a proof. One needs to construct a dual measure for each candidate set E of measure at most 1.835, namely a probability measure ν supported outside E for which Uν is non-negative on [−1,1]. We can do this when E is an interval, and it seems from numerics and theory that we can also do it when E is the union of a large interval and a small interval (which was the most likely candidate for a counterexample to the conjecture to be located), but we don't have a clear way forward to construct this dual measure for general E. (But in the case where E is the union of finitely many intervals, it seems the candidate measure should have a Cauchy-Stieltjes transform that looks something like a square root of a rational function with singularities at the endpoints of the intervals.)
TerenceTao
—
19:54 on 07 Mar 2026
| Reply

👍
1

📝
0

🤖
0
As a warmup, GPT-5.4 Thinking did some check on this note. Good news is there is no substantive error found. There are some minor things to fix, but we don't have to fix them now.
natso26
—
20:40 on 14 Mar 2026
| Reply

👍
0

📝
0

🤖
0
Professor Tao mentioned that the candidate dual measure λ(ε) should have a Cauchy–Stieltjes transform resembling a square root of a rational function with singularities at the interval endpoints. Has anyone attempted to make this ansatz explicit for the two-interval case (one large interval and one small interval near 1−ε)? The numerical evidence from the LP and AlphaEvolve work seems to consistently produce measures with that shape; a few atoms plus a continuous part with square-root behavior. It seems like writing down a closed-form family parametrised by ε and verifying Uλ(ε)≥0 analytically might be more tractable than pushing the numerics further. Is the obstacle here that the atom locations don't have clean closed forms, or is there a deeper issue?
MalekZ
—
17:12 on 17 Mar 2026
| Reply

👍
0

📝
0

🤖
0
I'm working on writing up the first variation result outlined in this thread.

Interestingly, GPT-5.4 Thinking has already found a gap. I used an "arbitrary" test measure ν to conclude Uλ≥0 from ∫Uλdν≥0. But there was a Hahn-Banach modification which constrains ν to not really be arbitrary!

Good news is this appears to be fixable with more arguments and hypotheses.
natso26
—
20:36 on 18 Mar 2026
| Reply

👍
0

📝
0

🤖
0
I am sorry! I am the one who's supposed to continue the work from the latest update on Jan 5. (The ball is in my court.)

Various things came up, mostly related to [728]'s AI solution back then, and then other things. Then I thought since the current state was messy, we might want to clean up to some kind of progress notes first. Then I thought it should be a good idea to wait for a new GPT model release (seemed imminent then). But this occurred a bit later than expected.

Good news: 1) Now GPT-5.4 has been released; 2) I actually now have an AI-led process ("near-autonomous") suitable for doing such things as compiling things into progress notes! Still, this project would still be considered larger than previous ones attempted with this process.

I'll find time to make progress here soon!
natso26
—
20:41 on 07 Mar 2026
| Reply

👍
0

📝
0

🤖
0
Against all (or at least some) odds, I have constructed a dual measure λ(ε) for ε=0.002.

We have minUλ(ε)≈1.5⋅10−4 at t≈0.989. That the minimum is positive has been validated on at least an order of 105 points (actually more and with a few other methods). In general, it is difficult to validate such things because the optimization generally overfits to the sampling, and "denser" sampling can reveal that the solution is actually invalid. (This is a general property optimization methods, which many people misinterpret in the case of AI as the AI being "tricky" or something like that.) However, in this case we seem to have enough margin (on the order of 10−4), and enough things check out that I think we can be reasonably confident this is valid.

This seems notable because AlphaEvolve was not able to achieve this task after running for over 24 hours. The algorithm is the "standard" cutting plane method for solving LP. However, it underwent several rounds of practical improvements, some coming from human suggestions. This highlights an interesting phenomenon that humans still possess some kind of "intangible" cognitive abilities that allow one to succeed in tasks that current LLMs may get stuck, even though the human does not clearly possess any extra knowledge in particular. On the other hand, without LLMs, I can say with confidence that this task is way out of reach for me, after seeing what is required in the final code.

In any case, the final code is a huge mess, and will need some improvements before I try to tackle lower ε such as 0.001. The runtime for ε=0.002 is 20-25 minutes and could go up with lower ε.

Description of λ(ε); Plot of λ(ε); Plot of Uλ(ε); Plot of Uλ(ε) (zoom); ChatGPT; Colab.
natso26
—
18:30 on 04 Jan 2026
| Reply

👍
2

📝
0

🤖
0
Wait, something very strange has just happened, because after 24 hours, AE has just reported constructing a primal measure with maxUμ(ε)≈−2.8×10−4 outside of [xL+ε,xR]∪[1−ε,1]. Here is the candidate:

[{'best_measure': {'discrete': [(0.8269121634120981, -1.0), (0.0021482374336376613, 0.9841438410522436), (0.0011875482476681922, 0.9875012314662565), (0.0013838133171846382, 0.9960541800161288), (0.00319963795475243, 0.9993548746166432), (0.007362636289093175, 0.9999405794148143)], 'continuous': [(0.6374729197720487, 0.7852693673372366, 0.9399498819286551), (1.0739314726524385, 0.9512166181174142, 0.9838542839858824), (1.236973123651978, 0.9854734797381937, 0.9931063255487078), (2.8943084557136225, 0.9929754891128861, 0.9959246744034838), (6.305518549205115, 0.9975757425023207, 0.9987133540092038)]}, 'info': {'is_admissible': True, 'max_potential': -0.0002833523044493986}}]

and here is the plot.

Unfortunately these two constructions contradict each other: ∫Uμ(ε)dλ(ε)=∫Uλ(ε)dμ(ε) should now be simultaneously positive and negative! I guess we need to get to the bottom of this...

EDIT: Preliminary analysis of the AE example suggests that it is in fact worse than the conjectural extremizer, with a total positive set of measure about 1.8361, compared to the extremizer 1.8344. There appears to be some sort of bug in my AE verification code, but have not nailed it down yet.

SECOND EDIT: OK, I tracked down the error: the vibe code for the verifier had cleverly managed to set ε equal to −0.002 rather than +0.002, rendering the entire run senseless. Given that it appears that there is (barely) a dual weight at this range, I will rerun the search for a primal with ε=0.001 and see what happens.
TerenceTao
—
19:13 on 04 Jan 2026
| Reply

👍
3

📝
0

🤖
0
Mathematical discussion at its best. Thanks to both of you for "performing" this here in the forum!
old-bielefelder
—
21:11 on 04 Jan 2026
| Reply

👍
0

📝
0

🤖
0
For what it's worth, AE has now also produced a viable weight λ(ε) for ε=0.002, claiming minUλ(ε)≥3.8×10−4:
[{'best_measure': {'discrete_parts': [(0.3455088854209601, -1.8061000004999002), (0.5751767608026921, 0.0263000004999), (0.00028910448988321905, 0.026863130099400376), (0.016053671544529087, 0.9979999995001), (1.0689113709431736e-05, 1.0000000004999001)], 'continuous_parts': [(0.042527505679321884, 0.7947464790425827, 0.8070676112835884), (0.009934652417916282, 0.8040879367695337, 0.8040925955633719), (0.005192240680136236, 0.8040925955633719, 0.804127415114407), (0.00935802967826106, 0.804127415114407, 0.8041320739082451), (0.012974118433324444, 0.8045945486686239, 0.8046485182066148), (0.046191311704892275, 0.8046485182066148, 0.8046545596252503), (0.012790680764289502, 0.8046545596252503, 0.8055596945529171), (0.023592242682416397, 0.8055596945529171, 0.8056257469281791), (0.001029934503877344, 0.8064625473323278, 0.8106586163358859), (0.02291534614904312, 0.8067230662729484, 0.8067284966653798), (0.005583869301016163, 0.8067284966653798, 0.8067710340340349), (0.02124025776382823, 0.8067710340340349, 0.8067764644264663), (0.0024321068687963776, 0.8067764644264663, 0.8073134973209191), (0.04075093590773043, 0.8070186194233637, 0.807019275128807), (0.014772243697922682, 0.8073141530263624, 0.807317472122879), (0.12113869661691763, 0.807317472122879, 0.8073175181802899), (0.03320795437651845, 0.8073175181802899, 0.8073180817709115), (0.10806537295102474, 0.8073180817709115, 0.8073181278283224), (0.11929183488824203, 0.8073315952648104, 0.8073344089803871), (0.04479566345176658, 0.8073344089803871, 0.8073737519085096), (0.021627213621214687, 0.8073622649670337, 0.807366895474437), (0.8507524414751924, 0.8077429229938331, 0.8077881323029654), (0.20364775447072883, 0.8143371395619201, 0.9038080469611189), (0.007341343211015569, 0.8810448747918207, 0.884623228380196), (0.3062405642769571, 0.9002540209345303, 0.9099693972995856), (0.22702132009570508, 0.9012744363692675, 0.9235297663693889), (4.573354428484476, 0.9273297676490931, 0.9282189454170567), (0.26111764466762283, 0.9315939973043751, 0.9318133136641716), (0.18663203116059596, 0.9318133136641716, 0.9318698922419824), (0.11549210134814415, 0.9318698922419824, 0.9319364353871358), (0.06628509386430582, 0.9319364353871358, 0.9327880940566486), (0.12154973893010781, 0.9327880940566486, 0.9328546372018021), (0.16020621926155842, 0.9328546372018021, 0.9329112157796128), (0.2553655683477129, 0.9329112157796128, 0.9331305321394093), (1.8713750356719827, 0.9331305321394091, 0.9333189906805238), (0.17456798601747722, 0.9337135091265176, 0.9352356169178782), (0.3295346829105154, 0.9345690518134381, 0.9408651654198456), (0.48602065109501474, 0.9409722686210414, 0.968231772833028), (0.006647888673185517, 0.9581937656214485, 0.9608306163921457), (0.002304252784042982, 0.9608306163921457, 0.9764469819393852), (0.1815805502273151, 0.9636902462223532, 0.9708049029562199), (0.3089175424225075, 0.9685859559973654, 0.9700841109029493), (0.6516570356049871, 0.9701767035636586, 0.98122150668761), (0.03819326143323973, 0.976315132320782, 0.9792078709702704), (0.0068253323081019735, 0.9764469819393852, 0.9790838327100824), (0.07472922247081759, 0.9792078709702704, 0.9944223941858618), (6.32134196702959e-05, 0.9808974246209095, 0.9914475794552879), (0.7770014156597694, 0.9814311007597097, 0.9850134768256965), (11.612761623156903, 0.9850022461042515, 0.9851357368996875), (0.5633794910475025, 0.9863718440334287, 0.9876269012310154), (1.0492754589396147, 0.9872281347003717, 0.9972789123170025)]}}]

Here is a plot.

It looks vaguely like λ(0) - a combination of delta spikes and something with a 1/((x−a)(1−ε−x))1/2 type behavior (creating some sort of mild singularity at 1−ε, but not at a), designed so that Uλ(ε) is zero on some big interval like [1−a,1−ε]. If we could guess a plausible ansatz for λ(ε) we might be able to figure out what it should be for arbitrarily small ε.
TerenceTao
—
06:46 on 05 Jan 2026
| Reply

👍
1

📝
0

🤖
0
Preliminary congrats on that side too! This is also essentially the same shape as my found solution. (At this point it's pretty much certain this is the right "shape" - but the numerical accuracy which proves/disproves validity can be relatively difficult to work out...)

First, I'll need to *verify* that. In my session with ChatGPT, my first solution found was actually invalid due to insufficient sampling - this leads to difficulties regarding how to overcome this (within resource constraints) which we finally achieved. So that's my first goal for now.

And then after that, maybe ε=0.001...

And just curious: can we manually set the verifier in AE? Presumably in this situation, a more robust verifier that's not just "vibe coded" by Gemini in the AE loop may be needed to get the right results!

[These software engineering-heavy tasks are not what I signed up for when doing "pure math", but it is what it is; I recall someone (maybe you?) saying the definition of a mathematician going forward may need to change anyway!]
natso26
—
10:26 on 05 Jan 2026
| Reply

👍
0

📝
0

🤖
0
A bit of bad news.

The AE example achieves min of about 3.86⋅10−4 on [xR,1−ε] (ε=0.002 here), consistent with your report. But it dips to min of about −0.013 on [−1,1]; the failure is near 1.

This zoomed plot shows the failure.
natso26
—
12:28 on 05 Jan 2026
| Reply

👍
0

📝
0

🤖
0
Interesting, that is a bug in the verifier, I will have to work to debug it. (The verifier can be either vibecoded through the interface or manually edited.) I did undersample in the region [1−ε,1] but I was sure that I at least verified it at x=1; I'll have to run the verifier offline to see what happened.

EDIT: OK, so it's not very interesting. In the interval [1−ε,1]=[0.998,1], I only verified non-negativity at the two endpoints 0.998 and 1, as well as the midpoint 0.999. AE was able to satisfy the non-negativity at the endpoints by creating small Dirac masses extremely close to these two endpoints, and (as the zoomed in plot shows) the potential was also barely non-negative at 0.999, thus passing all checks. I could fix the verifier by adding many more sample points (I'm also undersampling the region [-1,0]), but at this point I'm convinced that a dual weight exists for this value of ε, and am more interested in trying to locate it theoretically rather than numerically.
TerenceTao
—
16:00 on 05 Jan 2026
| Reply

👍
2

📝
0

🤖
0
Let's do theoretical! At the end of the day, numerics have already served its purpose. But at least we gain some experience in working with AE and/or potential pitfalls.
natso26
—
16:38 on 05 Jan 2026
| Reply

👍
2

📝
0

🤖
0
I have successfully cleaned up the code.

For reference: ChatGPT; Colab.
natso26
—
12:47 on 05 Jan 2026
| Reply

👍
0

📝
0

🤖
0
I have obtained dual solutions λ(ε) for ε=0.001 and ε=0.0005.

Here is some relevant data.

For ε=0.001:

Runtime: about 30 minutes. Minimum: Umin≈1.2⋅10−4 at t≈0.904.

Description of λ; Plot of λ; Plot of Uλ; Plot of Uλ (zoom).

For ε=0.0005:

Runtime: about 50 minutes. Minimum: Umin≈5.5⋅10−5 at t≈0.981.

Description of λ; Plot of λ; Plot of Uλ; Plot of Uλ (zoom).

Note that the runs were manually terminated once I think we have a good enough margin (admittedly this is rather ad hoc and has no basis in theory). Hence, Umin here doesn't have meaning, e.g. for asymptotic analysis. The runtime here was incomparable to the earlier ε=0.002 case because the code is a bit different.

I think we can be somewhat confident at this point that λ(ε) could exist for every ε>0. I'm not going to run the code for lower ε because the shape appears the same, going too low risks numerical issues which could invalidate the validation method (which has no basis in theory at the moment), and the runtime keeps increasing.

Colab.
natso26
—
16:44 on 05 Jan 2026
| Reply

👍
2

📝
0

🤖
0
Thanks for this!

I'm suspecting that the optimal λ=λ(ε) takes an explicit form, relating to a function of the form
f(z)=z+Aε(z−(xL+ε))(z−xR)(z−1)(z−a)(z−1+ε)‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾√

for some parameter Aε (I'm guessing it is a little bit larger than 1.2, but not sure on this - −Aε should be where Uλ(ε) attains a local minimum) and a suitable choice of square root. The measure λ should be like the imaginary part of this function, divided by π, so should take the form
λ=Res(f;xL+ε)δxL+ε+Res(f;xR)δxR+g(x)1[a,1−ε](x) dx

(possibly up to sign error) with g(x)=x+Aεπ(x−(xL+ε))(x−xR)(x−1)(x−a)(x−1+ε)‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾√, and its Hilbert transform Hλ should look like the real part, thus (up to some possible sign error and/or factor of π)
Hλ=x+Aε(x−(xL+ε))(x−xR)(x−1)|x−a||x−1−ε|‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾√1x∉[a,1−ε].

As usual, one should try to set Aε so that Uλ vanishes on [a,1−ε]. I think things are set up so that the derivative −Hλ of Uλ is positive just to the right of 1−ε and negative just to the left of a, so that we get a good shot at positivity of Uλ.

Note in this ansatz that the densty g of λ does not become singular at the right-endpoint 1−ε of the interval [a,1−ε], in contrast to the ε=1 case where there is a square root blowup at 1. Instead we have a square root vanishing at 1−ε but also a simple pole at 1 which in the limit ε→0 should recover the behavior of λ(0).

At this point I'm not confident in my ability to avoid sign errors, but given that ChatGPT was able to previously work out a viable λ in the ε=0 case, it might be able to confirm this ansatz for positive ε as well. Previously my ansatz was losing a factor of ε√ when evaluating Uλ near 1, but here I think one is instead gaining a factor of this form, so one is potentially in better shape (though I don't understand what Uλ is doing near the opposite endpoint -1, which is the other place where positivity could be in doubt.)
TerenceTao
—
21:13 on 05 Jan 2026
| Reply

👍
2

📝
0

🤖
0
Some progress on this.

In short: I'm not sure if such a measure λ(ε) exists for all ε>0 whose support avoids (xL+ε,xR)∪(1−ε,1) with the property that Uλ≥0 on [−1,1].

First, in order to perform these computations we need the conjectured minimizer to higher precision. We worked this out to be:
a∈[0.804461,0.804463],A∈[0.8245215,0.8245220],xL∈[−1.8081076,−1.8081072],xR∈[0.0263228,0.0263233].

This should be useful for other purposes as well (such as running AlphaEvolve for smaller ε). In practice we take the midpoint i.e. xL=−1.8081074, xR=0.02632305.

First try. We put supp λ on the endpoints {xL+ε,xR,1−ε,1} exactly (4 atoms). Then it reduces to a linear programming (LP) problem, and we use the cutting-plane method.

This turns out to work for large ε but not smaller ε. Specifically, it works for ε∈{0.1,0.05} but doesn't work for ε∈{0.02,0.01,0.005,…}.

Second try. We add another atom in the interval (xR,1−ε) to supp λ. For each position of this atom, we run an LP algorithm. A coarse sweep works for ε=0.02 but not ε=0.01. Then, we do local refinement to target the best region, which works for ε=0.01 but not for ε=0.005.

Third try. We add 2 atoms. But now optimization becomes tricky. We employ the Nelder-Mead method to optimize, but it still doesn't work for ε=0.005.

Fourth try. We use support augmentation: we start with 4 original atoms, find the "weakest" position where Uλ is minimized, and put an atom there. Then we iterate until Uλ≥0 on [−1,1].

For ε=0.005, a solution was found with 10 atoms.

For ε=0.002, the algorithm unfortunately stagnates at 26 atoms and was not able to find a solution.

Conclusion. I believe I have numerical evidence that such a measure λ(ε) exists for large ε, specifically ε≥0.005. But I am not sure whether it exists for all ε>0; perhaps the strategy so far is not smart enough in some way. In particular, AlphaEvolve might be smarter!

Details can be found in this ChatGPT chat.
natso26
—
11:43 on 31 Dec 2025
| Reply

👍
3

📝
0

🤖
0
Very nice natso26! I wonder whether it suffices to obtain Uλ>0 only on {−1}∪[0,1], since Tao showed that one may assume the support of a minimizing measure μ is contained in this set. If so, there may be room to take ε smaller.

In fact, using this observation, I was able to obtain a small improvement to the inf lower bound using two atoms, showing that it is at least 1.614 and that we may assume (−1.53,0]⊆{Uμ>0}. I am quite confident that this can be further improved by considering three or four atoms.

First, we performed a search for useful measures ν=δa+Bδb, with a≤0≤b and B>0, such that Uν(x)>0 for all x∈[−1,1]. I asked ChatGPT to generate code for a simple brute-force search and then modified it slightly for efficiency, it is available here. This produced the admissible region for (a,b) shown here. The minimum possible value of a is −1.518 at b=0.395, in agreement with J_Koizumi_144’s approach to the inf lower bound.

Next, we searched for measures ν of the same form, but requiring only that Uν(x)>0 for x∈{−1}∪[0,1]. This yields a larger admissible region, shown here. The minimum possible value of a is now −1.614, attained at b=0.60. For each a∈[−1.614,0], there is a corresponding interval (bmin(a),bmax(a)) of admissible values of b. Now assume that the supremum of [−1.614,−2‾√]∖{Uμ>0} exists and equals a0. Then, by the duality principle, we have (a0,0)⊔(bmin(a0),bmax(a0))⊆{Uμ>0}, and hence −a0+bmax(a0)−bmin(a0)≤|{Uμ>0}|. Plotting −a+bmax(a)−bmin(a), we find that it is at least 1.835 for a∈[−1.53,−2‾√], and that it decreases to 1.614 as a decreases further. This establishes the claimed bounds.
jspier
—
14:26 on 31 Dec 2025
| Reply

👍
2

📝
0

🤖
0
Ok, I think the logic is correct. Anyone else is welcome to check.

Logic: Let μ be a minimizer. By Tao's results, μ is supported on {−1}∪[0,1]. Assume for contradiction that |{Uμ>0}|<1.614. Then the largest interval (a0,0]⊂{Uμ>0} must have a0<1.614.

By the admissible plot, for such a0 there is a corresponding interval (bmin(a0),bmax(a0)) such that ν=νa0,b:=δa0+B(b)δb for b∈(bmin(a0),bmax(a0)) satisfies Uν>0 on {−1}∪[0,1].

By duality, ∫Uνdμ=∫Uμdν. LHS is >0 due to support assumptions. RHS is Uμ(a0)+B(b)Uμ(b). Uμ(a0)=0 because a0 is a boundary point. Thus, Uμ(b)>0.

We conclude (a0,0]∪(bmin(a0),bmax(a0))⊂{Uμ>0}. When we plot the length of (a0,0]∪(bmin(a0),bmax(a0)) as a function of a0, it comes out at least 1.614, a contradiction.

jspier, can you determine the exact digits so we know whether inf>1.614/1.615/1.613/…. Preferably, one more digit would be helpful for reference and other computations.
natso26
—
15:24 on 31 Dec 2025
| Reply

👍
1

📝
0

🤖
0
Thanks natso26! The inf lower bound is in fact ϕ=1+5√2≈1.6180. Indeed, if ν=12δ−ϕ+12δϕ−1, then using ϕ2−ϕ−1=0 one verifies that Uν(x)=0 for x∈{0,±1}. Moreover, since ϕ−1∈(0,1) and the unique critical point of Uν(x) is at −1/2∈(−1,0), we may conclude that Uν(x)>0 for all x∈(0,1).
jspier
—
15:26 on 01 Jan 2026
| Reply

👍
0

📝
0

🤖
0
That seems to give: 0<∫Uνdμ=∫Uμdν=0.5Uμ(−ϕ)+0.5Uμ(ϕ−1).

But you can't conclude either term must be positive from here?
natso26
—
15:47 on 01 Jan 2026
| Reply

👍
0

📝
0

🤖
0
Yes, one can conclude that either Uμ(−ϕ) or Uμ(ϕ−1) is positive whenever the support of μ intersects (0,1). The claim is that (−ϕ,ϕ−1) is an extreme point of the admissible region for (a,b), as suggested by the computations.
jspier
—
16:02 on 01 Jan 2026
| Reply

👍
0

📝
0

🤖
0
Sorry, I'm a bit confused on what's going on overall. I think:
1) You have argument (as I wrote out) which does prove inf>1.614 (subject to some numerical precision in the number 1.614).
2) You have given another, different argument inf>ϕ≈1.618. But this argument is much simpler and doesn't prove that.

Yes, either Uμ(−ϕ) or Uμ(ϕ−1) must be positive (I'm ignoring details regarding things like positive vs. nonnegaitve, < vs. ≤, etc. for now). But how does this connect to |{Uμ>0}|≥ϕ, which is not automatic? (Even though we are interested in finding measure ν such that Uν>0 on {−1}∪[0,1], this doesn't automatically translate to an inf bound.)
natso26
—
08:41 on 02 Jan 2026
| Reply

👍
0

📝
0

🤖
0
Ok, I think I rushed the explanation earlier. The original argument identifies the admissible region for (a,b) with a≤0≤b such that ν=δa+Bδb satisfies Uν(x)>0 for some B>0 and for all x∈{−1}∪[0,1]. With the original choice of sampling parameters, it appeared that the minimum possible value of a was −1.614 at b=0.60. However, these values were an artifact of the sampling.

After you asked for a more precise lower bound, I repeated the computation with increased sampling density. To my surprise, the minimum possible value of a decreased further and appeared to converge to a=−ϕ at b=ϕ−1. It turns out that this is the true infimum of the values of a for (a,b) in the admissible region. This conclusion is corroborated by the measure ν0=12δ−ϕ+12δϕ−1, which satisfies Uν0(x)≥0 for all x∈{−1}∪[0,1], and Uν0(x)=0 for x∈{0,±1}.

Therefore, we can repeat the initial argument with −ϕ and ϕ−1 in place of −1.614 and 0.6, respectively, and the argument will still go through. The only remaining caveat is that one must check that mina∈(−ϕ,−2√]−a+(bmax(a)−bmin(a))≥ϕ. I verified this inequality numerically to at least four digits of precision, but in principle it can be proved by choosing measures ν that are close to ν0 as a varies.
jspier
—
14:59 on 02 Jan 2026
| Reply

👍
1

📝
0

🤖
0
Ok, I'll take it for now that you've proved inf≥ϕ=(5‾√+1)/2≈1.618.

If this part is later written up then we can really check all details then. But in the meantime I think we can be reasonably confident given what you said.

Thanks!
natso26
—
15:52 on 02 Jan 2026
| Reply

👍
1

📝
0

🤖
0
Using jspier's approach with three atoms, the lower bound can be improved to at least 1.7. For a∈[−1.7,−2‾√], define a dual measure
λa=δa+kδ−2√−a+kδa+2.6,
where k is chosen so that Uλa(−1)=0. Then Uλa is positive on {−1}∪[0,1], which implies that at least one of {a,−2‾√−a,a+2.6} belongs to {Uμ>0}. By varying a, it follows that {Uμ>0} has measure at least 1.7−2‾√ outside (−2‾√,0], and hence inf≥1.7. Since I expect someone will quickly find a better strategy, I have not optimized the parameters.
J_Koizumi_144
—
14:00 on 02 Jan 2026
| Reply

👍
2

📝
0

🤖
0
This seems smart. Can you explain how you come up with these parameters in general? At least I can try to optimize it. The interesting part is it seems kind of "close" to the dual measure to the conjectured minimizer, which is worth investigating further.
natso26
—
14:28 on 02 Jan 2026
| Reply

👍
0

📝
0

🤖
0
Thanks. Basically, I found it by plotting the logarithmic potential of a linear combination of three Dirac measures in Desmos and then manually varying the parameters. For experimenting with linear combinations of Dirac measures, Desmos is a good tool for building intuition.
J_Koizumi_144
—
14:48 on 02 Jan 2026
| Reply

👍
2

📝
0

🤖
0
Did not cross my mind that an interactive graphing calculator is one possible tool (that doesn't overlap with other tools)!
natso26
—
14:55 on 02 Jan 2026
| Reply

👍
0

📝
0

🤖
0
Nice progress from both of you!

It is interesting that restricting to measures μ supported on {−1}∪[0,1] seems to help, at least for lower bounding the inf. This "breaks the symmetry" of the problem. On the other hand, for the task of finding a weight ν, it may not be as helpful: I think positivity at (−1,0) was already more or less automatic for convexity reasons once one had positivity at −1 and 0.

The fact that constructing a dual weight λ(ε) becomes hard for small ε matches with my theoretical experiments with trying to modify the ε=0 weight λ(0) by moving mass around to avoid [1−ε,1]. My calculations tended to gain a term of size O(ε) but then also lose a term of size O(ε√), indicating that the construction would not work for ε small enough.

If we become convinced that there is no weight λ(ε), then we should switch to the dual probem and try to construct a measure μ(ε) for which Uμ(ε)<0 outside of [xL+ε,xR]∪[1−ε,1] for that value of ε. That would almost certainly mean that our current upper bound 1.835... for the inf is in fact improvable very slightly. This would be unfortunate in the sense that it now becomes quite unlikely that we will be able to completely work out the extremizer, but still it is a surprising result and would be I think a good point to "declare victory" on the problem and maybe think about creating a paper.
TerenceTao
—
17:52 on 01 Jan 2026
| Reply

👍
2

📝
0

🤖
0
Ok. I am not yet convinced either way. In the calculations above, there are various things we haven't tried, including putting mass to the right of 1. (But I haven't done that yet because it's not clear what the "best" way to do it is.)

I agree that disproving the conjectured minimizer, if achieved, would be enough for "victory". But that may not be easy either. (Considering I have so far failed to find other local minima, but this is not very strong evidence.)

I was hoping you can run AlphaEvolve on small ε (maybe 0.002 or 0.001), with improved precision for xL,xR and sufficient sampling points. (I'm thinking maybe 10−4 could be enough because from the plot you gave earlier, it can't exploit the sampling very much unlike earlier experiments.) That could help in determine whether λ(ε) should exist, which I'm currently unsure either way.

Alternatively: if you have theoretical heuristics on how λ(0) should be modified, there could be ways to test that out numerically too, which I'll be happy to do!
natso26
—
08:58 on 02 Jan 2026
| Reply

👍
0

📝
0

🤖
0
OK, I just started an AE run with ε=0.002. I realized that there is no point checking positivity in the forbidden regions (−1,xR) and (1−ε,1), instead one should just check −1,+1, and some sample points in [xR,1−ε] and this should be good enough (I am going to try 5000 equally spaced points). EDIT: oops, the convexity goes the wrong way, I do need to check the forbidden regions after all. Updating code now.

In my theoretical experiments I took the portion of λ(0) in [1−ε,1] and replaced it with some equivalent amount of mass distributed either slightly to the left of 1−ε or slightly to the right of 1, and also adjusted the two big Dirac masses at xL+ε and xR appropriately. The latter adjustments tended to increase Uλ by ∼ε but the former adjustment tended to reduce it by ∼ε√, resulting in a net loss when ε was small. So my conclusion was that this type of modification did not work for small ε. But potentially a more significant perturbation of λ(0) could work.
TerenceTao
—
18:26 on 02 Jan 2026
| Reply

👍
1

📝
0

🤖
0
AE is still chugging along. After 7 hours, its best attempt is

[{'best_measure': {'discrete_parts': [(0.3731882881770592, -1.806100000999), (0.5241508440572373, 0.026300000999), (4.467787208012591e-06, 0.6168387288217025), (1.611046135311908e-06, 0.7658417839881596), (1.484516983646001e-05, 0.7659828334256523), (0.0005065715725557909, 0.7701741229138237), (2.8787788213344614e-05, 0.7832781769822117), (1.0903567776944535e-06, 0.7935577020020302), (0.0005132882450796192, 0.7981900409276943), (0.00015926971808661428, 0.8663315489621293), (2.969033967292002e-05, 0.8667846935458583), (0.0005042927469189352, 0.9085133418043203), (4.0875945079921064e-05, 0.9191469410838441), (1.2621784755007757e-07, 0.9371091675703764), (8.385696017796744e-05, 0.9392835307395657), (0.006934694994878188, 0.9472631225763004), (5.172119321378422e-05, 0.9545150508741439), (0.001968389211361791, 0.9673352775404732), (0.006689069536459032, 0.9744186046511627), (1.4309731030583893e-05, 0.9789792495476484), (0.006706945556281067, 0.9835589222373805), (0.013463893004241095, 0.9925742574257426), (0.005789089750614169, 0.9972814870395633), (0.0009355814711160167, 0.997999999001), (0.009170097260246977, 1.000000000999)], 'continuous_parts': [(0.2991485760766823, 0.7760791800702427, 0.7776921492886546), (0.35830600392052875, 0.7815725014884682, 0.7818585681695402), (0.00015661762320629696, 0.7820259053846954, 0.7838248108746202), (2.2416060829476345, 0.7879155073358589, 0.7883770525632584), (18.958387615223163, 0.8327647259179386, 0.8335178765639658), (2.010519432765325, 0.8627225282467257, 0.8633051163312984), (22.627801602396612, 0.8896260589206523, 0.8901904548408156), (4.887369335226809, 0.9255584828494691, 0.9280586589606775), (7.014824868344669, 0.9594047951859929, 0.9604010070087236)]}}]

for which Uλ is lower bounded by -0.00083. Here is a plot; it is rather low resolution on [-1,0] because I decided to only sample a small number of points here due to the convexity of Uλ. The loss is a lot closer to ε than ε1/2 so it does suggest that my naive attempts to move mass around were inefficient.
TerenceTao
—
01:47 on 03 Jan 2026
| Reply

👍
1

📝
0

🤖
0
Hmm. Some observations:
1) It’s trying to produce a flat {Uλ=0} region again. This looks structurally important, but could be a nightmare for numerical optimizations.
2) There is indeed a discrete mass to the right of 1 (if I’m reading correctly that’s 1.000000000999). I’ll try to think how to incorporate that intelligently.
3) It’s still not obvious whether λ(ε) exists for small ε>0 either way. Either it exists but the right perturbation is yet to be found, or the asymptotics doesn’t work out for yet unknown reasons.
natso26
—
05:38 on 03 Jan 2026
| Reply

👍
1

📝
0

🤖
0
AE continues to improve the construction; it still cannot achieve positivity, but narrowed the lower bound for Uλ down to -0.000262. The description of λ is now rather lengthy, and the plot of Uλ is extremely flat near 1 again.

I'll keep the run going for now, but will start a separate run on the primal problem: trying to construct a probability measure μ on [−1,1] which is negative outside of [xL+ε,xR]∪[1−ε,1]. In principle, linear algebra duality tells us that at least one of these problems has to succeed. (It may also be that some more dedicated linear programming method will be more effective here than AE, but I have little experience with large-scale numerical linear programming, though I know that guaranteeing numerical accuracy can become an issue.)
TerenceTao
—
17:01 on 03 Jan 2026
| Reply

👍
2

📝
0

🤖
0
Thanks! The lambda.txt gets 403 access denied.

That's interesting. It's very close to 0. Either ε=0.002 is at the edge of being impossible, or AE is encountering some numerical issue e.g. unclear gradient direction that prevents improvement.
natso26
—
17:09 on 03 Jan 2026
| Reply

👍
0

📝
0

🤖
0
It should be visible now, but just in case, here is the data:

[{'best_measure': {'discrete_parts': [(0.3738164710656476, -1.8061000009900001), (0.524225822836817, 0.02630000099), (2.1985491343290817e-07, 0.7311288479657718), (9.140778798105392e-06, 0.7409617017554078), (3.656311519242157e-05, 0.7462465767554078), (8.043034310386537e-06, 0.7506960989885813), (3.8145550155051e-06, 0.7527530528066934), (9.140778798105392e-06, 0.7551867017554077), (9.140778798105392e-06, 0.7554117017554078), (1.8057673664151058e-06, 0.7587726998491704), (6.304561062944435e-05, 0.7598908594815826), (3.208510437406948e-05, 0.7618738751814225), (0.00015929250131633033, 0.763358778625954), (2.8744848122691466e-05, 0.7656249999999999), (0.00011401382011936675, 0.7672426504068045), (4.0201997433601056e-05, 0.7688359328434221), (7.545496385980123e-06, 0.7700068558614555), (8.043034310386537e-06, 0.7706960989885813), (0.00025332201832703813, 0.7710831778494807), (5.9803028027869735e-05, 0.7719320783645656), (2.4637000404014168e-05, 0.7725925925925927), (0.00012666100916351906, 0.7730138166894658), (2.6810610809800094e-05, 0.7744559953434226), (9.140778798105392e-06, 0.7751867017554077), (4.014766975655496e-05, 0.775633293124246), (6.032330851808046e-05, 0.7763820213799804), (6.03233085180805e-05, 0.7777524427158542), (2.463675542221734e-05, 0.7779383738396232), (0.00014782151246049133, 0.7787418655097614), (3.0515505336438375e-06, 0.778894968140873), (7.391075623024566e-05, 0.7795522865067959), (7.391075623024566e-05, 0.7799422733923214), (0.0001356524571712997, 0.7832957110609481), (7.545496385980123e-06, 0.7844568558614555), (3.3513182690525263e-06, 0.786954843140873), (3.695537811512283e-05, 0.7880522865067958), (0.00012471621955222493, 0.7882523660517475), (2.4637000404014168e-05, 0.7885052673284191), (2.9751108460249957e-05, 0.7888129208043694), (0.00023800886768199966, 0.7894041708043694), (0.0010479899160660798, 0.7900763358778629), (5.9803028027869735e-05, 0.7919320783645656), (3.208510437406948e-05, 0.7923752511141647), (1.4875554230124979e-05, 0.7960379208043694), (7.391075623024566e-05, 0.7969422733923213), (0.00019003326173639258, 0.7976346911957949), (2.463675542221734e-05, 0.7979383738396232), (7.391075623024566e-05, 0.800818553888131), (4.9274056309730685e-05, 0.8015434944399475), (2.4636699920515042e-05, 0.8019471775934551), (4.9274000808028337e-05, 0.8025925925925927), (9.750178610981327e-05, 0.8027169014084508), (3.907505395457998e-08, 0.8034371775934552), (9.935230229819691e-05, 0.8036072144288574), (3.695537811512283e-05, 0.8050522865067957), (0.0001260912212588887, 0.8058608058608059), (0.00023801048440543266, 0.805991388312555), (1.359652945108477e-05, 0.8080657639973731), (5.9502216920499914e-05, 0.8083204208043694), (1.4875554230124979e-05, 0.8104879208043695), (0.00011900443384099983, 0.8166291708043695), (3.907505395457998e-08, 0.8204371775934551), (0.00028561128790777245, 0.825067466934096), (0.00019650050725982828, 0.8259489732373598), (0.00010877223560867816, 0.8276256389973732), (1.359652945108477e-05, 0.8280657639973731), (0.00013099394351338335, 0.8286157561306216), (4.7508315434098146e-05, 0.8305318060627992), (0.00015445963792986542, 0.8329467692798214), (0.0005712225758155449, 0.8334898662741452), (0.0005712225758155449, 0.8335081853049925), (0.0005712225758155449, 0.8335378261195442), (0.0005712225758155449, 0.8335857859649431), (2.3754157717049073e-05, 0.8364818060627993), (2.719305890216954e-05, 0.8380657639973731), (2.3754157717049073e-05, 0.841497926972718), (0.00028561128790777245, 0.842067466934096), (0.00019650050725982828, 0.8429489732373597), (5.438611780433908e-05, 0.8480657639973731), (4.7508315434098146e-05, 0.8505318060627992), (1.2187777862484982e-05, 0.8522997264182063), (1.2187723263726669e-05, 0.8525053068943595), (0.0001894503495367555, 0.8553888130968623), (0.0001900332617363927, 0.8570009930486593), (0.00014782151246049133, 0.8585461689587419), (9.750178610981335e-05, 0.8591117917304746), (0.00011406133332691908, 0.8594024604569427), (6.500082720981137e-05, 0.8614401786069819), (0.00013000274500981533, 0.8614750045363068), (1.2187777862484982e-05, 0.8627398514182062), (6.433215650774816e-06, 0.8636110861759425), (4.7508315434098146e-05, 0.8649818060627993), (1.2187723263726669e-05, 0.8695053068943595), (7.89823789531571e-05, 0.8711150411483843), (0.0008852150809273711, 0.871431828442438), (4.578730035413308e-05, 0.8714595190380761), (4.8750893054906677e-05, 0.8719958791208787), (1.2287218794055335e-05, 0.8720199022489984), (5.8330829591211494e-05, 0.8732750283785671), (0.00010376470563393857, 0.8754105173408162), (2.4375446527453338e-05, 0.8754553068943596), (0.0011057533053441995, 0.8766233766233766), (6.433215650774816e-06, 0.8780610861759426), (6.417020874813896e-05, 0.8789536951070372), (0.0001579647579063142, 0.8804167056822254), (0.0001579647579063142, 0.8810840792389744), (1.604248794768229e-05, 0.8810975609756097), (0.0001579647579063142, 0.8811956621048516), (1.203193020011417e-05, 0.8825975609756096), (0.0004150588225357543, 0.8849703923408163), (0.0001579647579063142, 0.885202817546913), (0.0011026557163859758, 0.8853053319565716), (4.8750893054906677e-05, 0.8864458791208788), (7.89823789531571e-05, 0.8881150411483842), (4.578730035413308e-05, 0.888459519038076), (0.0003159295158126284, 0.8895951294165049), (0.0003159295158126284, 0.8896846119273211), (0.0001579647579063142, 0.894076923796913), (0.0011057533053442008, 0.8941794382065703), (0.0001579647579063142, 0.8948667056822255), (0.00010376470563393857, 0.8954105173408162), (0.0001579647579063142, 0.8980840792389743), (0.00010376470563393857, 0.8981855173408162), (0.0001579647579063142, 0.8981956621048515), (7.839132501268562e-06, 0.8985365853658536), (2.457443758811067e-05, 0.8991183066517289), (1.203193020011417e-05, 0.8995975609756095), (0.0001579647579063142, 0.8996150411483843), (0.0011057533053442008, 0.8996995991983965), (1.2287218794055335e-05, 0.9004138213048063), (0.0007370571416379783, 0.9024390243902439), (4.914887517622134e-05, 0.9032077376765851), (0.00023591124359861876, 0.9051252324290031), (0.00023591124359861876, 0.9051506870871351), (4.914887517622134e-05, 0.9051737379672096), (0.00023591124359861876, 0.905191873589165), (4.914887517622134e-05, 0.9052100092111202), (0.00023591124359861876, 0.9052330600911946), (4.914887517622134e-05, 0.9052414210297735), (0.00023591124359861876, 0.9052585147493268), (0.000229099800111464, 0.9068219633943428), (0.00018134173094278596, 0.9097154072620219), (2.457443758811067e-05, 0.9114008066517288), (0.00010376470563393857, 0.9126355173408163), (0.00040736773346300084, 0.9133935307108783), (0.00040736773346300084, 0.9134075877088348), (0.00040736773346300084, 0.9134319351434972), (0.00040736773346300084, 0.9134600491394107), (0.00040736773346300084, 0.9134843965740735), (0.00040736773346300084, 0.9134984535720299), (2.457443758811067e-05, 0.9136423261485562), (8.02127609351737e-06, 0.9185365853658536), (0.001222103200389001, 0.9195835709050733), (0.00012610173030060408, 0.9325147723391785), (0.001222103200389001, 0.9340335709050728), (6.305086515030204e-05, 0.9347972723391784), (0.001261866650759676, 0.9410609037328098), (4.355425962996436e-06, 0.9420592131820235), (0.0007762900082516765, 0.9431354662130674), (0.0007167189789634878, 0.9456215253150134), (0.00029454994283311357, 0.947620401097358), (5.792312156687692e-05, 0.9510552040866276), (2.5710742713257365e-06, 0.9535592131820235), (0.00036268346188557177, 0.9542984732824429), (6.305086515030204e-05, 0.9547972723391784), (2.782031888249759e-05, 0.9566222807017541), (0.0005214532412617226, 0.9593580274901737), (0.0011781997713324543, 0.9593846955026873), (0.0011781997713324543, 0.9595826324266917), (0.00029454994283311357, 0.959902901097358), (0.0011781997713324543, 0.9602231697680249), (0.0011781997713324543, 0.9604211066920272), (0.00051887590479693, 0.9604477747045428), (4.355425962996436e-06, 0.9635592131820235), (0.0001534226870822411, 0.9650122807017543), (0.0005890998856662271, 0.966044151097358), (0.0009843353928440548, 0.9665075808451645), (0.0001431048322915182, 0.9676319354838714), (0.0009843353928440548, 0.9686629742357825), (2.5710742713257365e-06, 0.9705592131820234), (6.968681540794297e-05, 0.9716190881820236), (1.7311230379098998e-05, 0.9726005450186356), (0.00013934751453987428, 0.9731629439332167), (2.782031888249759e-05, 0.973622280701754), (0.00020906332484723638, 0.9746816586921843), (0.00015911004871031197, 0.9747731756503274), (6.032330851808046e-05, 0.9749103942652327), (0.0008362532993889458, 0.9761904761904763), (0.0006969057848490713, 0.9768048855483853), (0.0001589901169905958, 0.9774327331825682), (2.256374335773925e-05, 0.9779353484920877), (0.0002787530188785872, 0.9781529294935452), (1.3616891911834167e-05, 0.9783754734920876), (0.0004181266496944731, 0.9787057797007329), (0.0004181266496944731, 0.9795134443021769), (4.355425962996436e-06, 0.9805592131820234), (1.7421703851985743e-05, 0.9820592131820235), (0.000662232987553436, 0.9832260714719284), (0.0007955247086416983, 0.9832332384747263), (0.0007955247086416983, 0.9832446688244328), (0.00031822009742062395, 0.9832589222373803), (0.00031800890702825285, 0.9832917730028322), (4.581192563912917e-05, 0.9832983792263217), (0.00020262801300829214, 0.9834704647740375), (0.0004052560260165843, 0.9863606789868021), (0.0009349185910211584, 0.9868131868131865), (0.0004052560260165843, 0.989520418180931), (0.0004052560260165843, 0.9895345418130365), (0.0004052560260165843, 0.9895590046614312), (0.0004052560260165843, 0.9896258384061435), (0.00015911004871031197, 0.9917731756503273), (3.4843407703971486e-05, 0.9920592131820235), (0.0004809221067315235, 0.9936280624699315), (0.0004809221067315235, 0.9953038475649351), (0.0004809221067315235, 0.9953199847247943), (0.0004809221067315235, 0.9953401074340005), (0.0004809221067315235, 0.9953602301432067), (0.0004809221067315235, 0.9953853227511585), (0.00020262801300829214, 0.9957529647740375), (0.000492807402227878, 0.9968877106847832), (0.0004913523179295729, 0.9973861219803438), (0.0004173945236680979, 0.9974568520987828), (0.0010554126075798937, 0.99799999901), (0.009171409025188289, 1.00000000099)], 'continuous_parts': [(10.028728996060421, 0.8248151688168306, 0.8249575653697836), (20.434611210455323, 0.8328365672490459, 0.8329559035281486), (28.23063602458222, 0.83309071811348, 0.8331918843684246), (9.066846049624752, 0.8418076155389229, 0.8419651186476913), (18.927249186605415, 0.8673350913080745, 0.8674519337815308), (17.893485903683843, 0.9242301539727938, 0.9243667515264472), (20.61419298456318, 0.927484069676008, 0.9276026387804406), (14.818799204010043, 0.9371291608622454, 0.9372941004344151), (11.368363043723098, 0.9487103633107273, 0.9488469335460842), (11.071789047214567, 0.952410838146935, 0.9525510666149706), (35.951403641933894, 0.9721526476593664, 0.9722456902907716), (15.378710882581311, 0.9831554109920874, 0.9833661506229853), (27.002880808801397, 0.9915661865805242, 0.9916908567877868), (36.29138110376971, 0.9927276117614351, 0.9928203735865498), (69.011209580625, 0.9973861219803435, 0.9974568520987828)]}}]
TerenceTao
—
18:46 on 03 Jan 2026
| Reply

👍
2

📝
0

🤖
0
Thanks. I seem to still get 403 access denied.
natso26
—
18:56 on 03 Jan 2026
| Reply

👍
0

📝
0

🤖
0
Hmm, for some reason wordpress seems to think that txt files are more of a security risk than say png or pdf files. Ah well.

After 8 hours, AE has come close, but hasn't quite, found a measure μ with {Uμ>0} confined to [xL+ε,xR]∪[1−ε,0]. The following example has Uμ≤0.000229 outside of this region:

[{'best_measure': {'discrete': [(0.8263625635529295, -1.0)], 'continuous': [(2.179351684404958, 0.9961859278249665, 0.9999999123719181), (0.6368034604344739, 0.7821871237386602, 0.9999998619243384), (2.132611945518574, 0.9919560262089107, 0.9999999762953526), (2.3372917489709266, 0.9818379449435556, 0.9858883136481454)]}, 'info': {'is_admissible': True, 'max_potential': 0.0002291466883918521}}]

Here is a plot of Uμ. It looks very similar to the conjectured infimizer.

I still have no idea which of the two linear programs will actually succeed; they are both so close to the edge. (There is probably some clever Bregman-type scheme to solve for both μ and λ simultaneously that is fast and accurate, but I am not an expert in these sorts of things.)
TerenceTao
—
02:25 on 04 Jan 2026
| Reply

👍
2

📝
0

🤖
0
I’ll try to explore how LP can be leveraged here. No promise!
natso26
—
05:21 on 04 Jan 2026
| Reply

👍
0

📝
0

🤖
0
Regarding Wordpress, it seems that svg and txt files are disallowed in upload for security reasons. The likely explanation is that these can contain markup/text that are close to “web content”, which can become an attack surface area in browser environments. Always interesting to learn about cybersecurity! ChatGPT.
natso26
—
08:02 on 04 Jan 2026
| Reply

👍
0

📝
0

🤖
0
Following J Koizumi's approach which builds on jspier's approach, I've proved inf≥1.7205 with empirical numerical verification (gives enough confidence in practice but for a proof one needs to do further rigorous computations, which can be done later).

This is pretty close to the conjectured inf of ≈1.835, suggesting maybe this approach can get even closer?

The idea is to optimize 3 atoms. For d=2.6476 and M=1.7205, for each a∈[−M,−2‾√], there exist k(a) and m(a) such that the measure
λa=δa+k(a)δ−2√−a+m(a)δa+d

satisfies Uλa>0 on {−1}∪[0,1].

As with J Koizumi's logic, one of a,−2‾√−a,a+d must be in {Uμ>0} for a minimizer μ. Since we know (−2‾√,0]⊂{Uμ>0}, |{Uμ>0}| is at least 2‾√+(M−2‾√)=M.

Joint with ChatGPT; Colab notebook.
natso26
—
18:02 on 02 Jan 2026
| Reply

👍
2

📝
0

🤖
0
Thanks for working on the optimization. After writing my previous comment, I realized that shifting in the same direction gives a better bound. For a∈[−1.75,−2‾√], define
λa=δa+0.7δa+1.75+0.44δa+2.65.
Then Uλa>0 on {−1}∪[0,1] (plot), so at least one of {a,a+1.75,a+2.65} lies in {Uμ>0}. This yields inf≥1.75.
J_Koizumi_144
—
18:53 on 02 Jan 2026
| Reply

👍
3

📝
0

🤖
0
Thanks natso26 and J_Koizumi_144 for further optimizing the inf lower bound! We obtain a small additional improvement using this last shifting construction by J_Koizumi_144. For a∈[−1.7877,−2‾√], define the measure
νa=δa+1.27383δa+1.7877+0.34979δa+2.73436.

Then Uνa>0 on [−1,1], as can be verified here. This implies that inf≥1.7877.

Two remarks about this construction. First, it is interesting that Uνa is positive on the entire interval [−1,1], rather than only on {−1}∪[0,1]. So perhaps it is indeed not helpful to focus on this smaller region in some situations. Second, despite some effort, I could not make the construction work with −1.7878 in place of −1.7877 and believe this is close to the limit for this particular approach (with three atoms).

Finally, this approach in general involves a family of measures
νb=∑ipi(b)δri(b)

for b in some interval, satisfying Uνb>0 on {−1}∪[0,1], where the atoms move in a diagonal direction, that is, ri(b)=si±b for every i. It turns out that it is also helpful to fix the location of some of the atoms, as this can provide more information about the minimizing measure μ. An example of this is the proof that we may assume (−1.53,0]⊆{Uμ>0}, which uses a family of measures composed of two atoms νa,b=δa+B(a)δb, where b∈[bmin(a),bmax(a)] and a is fixed. I believe that the same sort of family of measures, but with three atoms, may allow us to show that (−1.708,0]⊆{Uμ>0}.
jspier
—
01:32 on 03 Jan 2026
| Reply

👍
3

📝
0

🤖
0
Thanks all! I’ll try to verify/optimize these progress. In particular there’s an interesting question of can this force accumulation of (−M,0]⊂{Uμ>0} where M is sort of large. That seems more sophisticated but I’ll think about it. Essentially any sort of argument that looks like it can get close to ≈1.835 could help in determining what shape the final argument might be (if we eventually get to it)!
natso26
—
05:27 on 03 Jan 2026
| Reply

👍
1

📝
0

🤖
0
It turns out that optimizing this family gets numerically complicated (one reason being there's an extra degree of freedom). But it has been done.

For d1=1.790312, d2=2.735313, and M=1.790289, we have reasonable confidence from numerical optimization that for each a∈[−M,−2‾√], there are k1(a),k2(a)≥0 such that the measure
λa=δa+k1(a)δa+d1+k2(a)δa+d2

attains Uλa>0 on {−1}∪[0,1].

As before, this proves that inf≥M.

Note that due to the complexity of the algorithm and runtime, the best bound that can come out of this method is likely not this exactly but it seems to be lower than 1.791.

To report with reasonable confidence, I think I can say inf≥1.7902 but will refrain from claiming more digits.

ChatGPT; Colab. This particular session is complex and lengthy. It may be of interest to someone learning more about numerics and/or working with LLMs.
natso26
—
17:53 on 03 Jan 2026
| Reply

👍
1

📝
0

🤖
0
Nice work, natso26! I had already given up on the three atom approach, and I am surprised that you managed to push it further. This motivated me to look at the four atom case. However, before doing so I'm going to show that we may assume [−1.708,0]⊆{Uμ>0} for a minimizing measure μ.

For a∈[−1.708,−2‾√] and b∈[0,1.836+a], consider
νa,b=δa+(1.395−b)δb+Cδ1.071−b,

where C>0 is chosen so that Uνa,b(−1)=0.0001. As can be seen here, we have Uνa,b>0 on {−1}∪[0,1].

We now claim that [−1.708,0]⊆{Uμ>0}. Assume otherwise, then the infimum of {Uμ>0} is a0∈[−1.708,0], with Uμ(a0)=0. Since Uνa0,b>0 on {−1}∪[0,1] for every b∈[0,1.836+a0], by the duality principle, either b or 1.071−b belongs to {Uμ>0}. Note that both b and 1.071−b are positive and are never equal to each other. It follows that {Uμ>0}∩(0,+∞) has measure at least 1.836+a0. Since we also have (a0,0]⊆{Uμ>0}, we conclude that |{Uμ>0}|≥1.836, and therefore μ cannot be a minimizing measure.

Now we turn to the four atom approach. We are going to show that inf≥1.8. For a∈[−1.8,−2‾√], consider
λa=δa+1.08δa+1.8+0.2107δa+2.66996+0.1326δa+2.79.

As can be checked here, we have Uλa>0 on [−1,1]. Therefore, for a∈[−1.8,−1.708), at least one of a, a+1.8, a+2.66996, a+2.79 belongs to {Uμ>0}. Note that for a in this range these four numbers are distinct, and none of them lies in [−1.708,0]. It follows that |{Uμ>0}∖[−1.708,0]|≥1.8−1.708. Since we already know that [−1.708,0]⊆{Uμ>0}, we conclude that inf≥1.8.

Finally, I would like to mention that I did not optimize these parameters, and there is likely room for further improvement. The measures above were obtained using the program that I shared earlier, together with some experimentation in Desmos.
jspier
—
02:06 on 04 Jan 2026
| Reply

👍
2

📝
0

🤖
0
Nice work! I’m going to assume that these results are correct i.e. 1) that a minimizer μ satisfies [−1.708,0]⊂{Uμ>0}, 2) that inf≥1.8. It feels like we kind of want to turn this into some kind of iterative algorithm that uses more and more atoms to automatically improve, but at present it’s not at that stage yet. (At least I don’t know how to turn the 4 atoms into a stronger [−M,0]⊂{Uμ>0} bound.)
natso26
—
05:19 on 04 Jan 2026
| Reply

👍
1

📝
0

🤖
0
Show 9 more comments
All comments are the responsibility of the user. Comments appearing on this page are not verified for correctness. Please keep posts mathematical and on topic.
Currently logged in as Hua Xu (logout)
Your comment will go into a moderation queue and not appear until approved.

Post comment
Back to the forum