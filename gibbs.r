#
# gibbs.r
#
# This is an R implementation of a regime-switching auto-regressive time series
# model described by James H. Albert and Siddhartha Chib in the 1993 paper
# "Bayes Inference via Gibbs Sampling of Autoregressive Time Series Subject to
# Markov Mean and Variance Shifts"
#
# The functions contained in this source code are for simulating the full time
# series with given parameters and for simulating from the marginals of each
# parameter contingent on the others. The latter are used for Gibbs sampling
# with the aim of estimating unknown parameters of an empirical time series.

library(MASS) # For the mvrnorm function (multivariate normal)
library(mixtools) # For finding good starting values for the Gibbs sampler



# Try to get a graphical progress bar
if (R.Version()$os == 'mingw32') {
	# Microsoft Windows
	progress.bar = winProgressBar
	set.progress.bar = setWinProgressBar
} else if (require(tcltk)) {
	# UNIX? Try Tkinter
	progress.bar = tkProgressBar
	set.progress.bar = setTkProgressBar
} else {
	# Who knows? Default to text
	progress.bar = txtProgressBar
	set.progress.bar = setTxtProgressBar
}



rsar.sim = function(phi, mu, gamma, sigma, tau, k, n=1000, burn=0)
#
#	y ~ p(y | phi, mu, gamma, sigma, tau, k)
#
# Simulate a regime switching auto-regressive time series given the parameters.
# The first step is to generate the Markov chain and then generate the time
# series for each data point according to the corresponding state. 
{
	# phi   : auto-regression coefficients (vector)
	# mu    : state 0 mean
	# gamma : state 1 added mean
	# sigma : state 0 variance
	# tau   : state 1 added variance
	# k     : Markov kernel (vector)
	# n     : sample size
	# init  : initial value
	# burn  : simulation burn-in size

	m = n+burn # number of simulated points
	s = sample(0:1, 1) # Markov chain (2 states coded in 0 and 1)
	y = rnorm(1, mu+gamma*s, sigma+tau*s) # initial value

	# (1) Generate the Markov chain

	u = runif(m) # transition "attempts"
	for (i in 2:m)
	{
		if (s[i-1])
		{
		 if (u[i] < k[1])
			s = c(s, 1)
		 else
			s = c(s, 0)
		}
		else
		{
		 if (u[i] > k[2])
			s = c(s, 1)
		 else
			s = c(s, 0)
		}
	}

	# (2) Generate the time series

	u = rnorm(m) # white noise
	for (i in 2:m) 
	{
		r = min(length(y), length(phi)) # prevent out-of-bounds

		mu.b = mu + gamma*s[(i-1):(i-r)]
		sigma.i = sigma + tau*s[i]
		y.b = y[1:r] - mu.b
		y.i = mu + gamma*s[i] + sum(phi[1:r]*y.b) + sqrt(sigma.i)*u[i]

		y = c(y.i, y) # built in reverse
	}

	# Truncate the burn-in
	# Re-reverse x vector
	# Return time series

	list(ts=ts(rev(y[1:n])), s=s, n=n, burn=burn,
	phi=phi, mu=mu, gamma=gamma, sigma=sigma, tau=tau, k=k)
}



s.cond = function(y, phi, mu, gamma, sigma, tau, k, s)
#
#	s ~ p(s | y, phi, mu, gamma, sigma, tau, k, s)
#
# Generate a Markov chain from 0, 1. The chain is not simulated ex-nihilo but
# is a modification of the previous chain. The distribution of any one state is
# Bernoulli with the probability of remaining in the current state calculated
# from what is given in the data y, the states inside of the previous chain,
# and the parameters phi, mu, sigma, gamma, tau, k, s.
{
	# y     : complete time series (vector)
	# phi   : auto-regression coefficients (vector)
	# mu    : state 0 mean
	# gamma : state 1 added mean
	# sigma : state 0 variance
	# tau   : state 1 added variance
	# k     : Markov kernel probabilities (vector)
	# s     : Markov chain will be modified (vector)

	n = length(y)
	r = length(phi)

	# De-trending joint density of y[i] given that state s[i] = S

	joint.dens = function(i, S)
	{
		ss = s # Almost the same
		ss[i] = S # We fix one state

		dens = function(j)
		{
			S = ss[j]
			y.hat = 0
			if (i > 1)
			{
			 # Calculation boundary
			 m = min(r, j-1)
			 # Take out all the means
			 mu.hat = mu + gamma*ss[(j-m):(j-1)]
			 # Predict this point in the auto-regression
			 y.hat = sum(phi[m:1]*(y[(j-m):(j-1)] - mu.hat))
			}
			# Return the density of this point in state S
			dnorm(y[j], y.hat+mu+gamma*S, sqrt(sigma+tau*S))
		}
		
		# Calculation boundary
		m = min(r, n-i+1)
		# Storage
		joint = numeric(m)
		# Densities of the next m points
		for (j in 1:m) joint[j] = dens(i+j-1)
		# Joint density is the marginal product by independence
		prod(joint)
	}

	# A matrix is easier to work with here than the vector
	K = matrix(c(k[1], 1-k[2], 1-k[1], k[2]), nrow=2)
	# Markov transition probability, P(s.i | s.j)
	P = function(s.i, s.j) K[s.i + 1, s.j + 1]
	# Working back to front	
	for (i in n:1)
	{
		# Boundary points are special cases

		if (i == 1) # First
		{
		 p0 = joint.dens(i, 0)*P(0, s[i+1])
		 p1 = joint.dens(i, 1)*P(1, s[i+1])
		}
		else
		if (i == n) # Last
		{
		 p0 = P(s[i-1], 0)*joint.dens(i, 0)
		 p1 = P(s[i-1], 1)*joint.dens(i, 0)
		}
		else # Interior point
		{
		 p0 = P(s[i-1], 0)*joint.dens(i, 0)*P(0, s[i+1])
		 p1 = P(s[i-1], 1)*joint.dens(i, 1)*P(1, s[i+1])
		}

		# Estimate probability
		if (s[i] == 0)
			theta = p0/(p1 + p0)
		else
			theta = p1/(p0 + p1)

		# Simulate this point's state
		remain = rbinom(1, 1, theta)
		if (remain == 0) # switch
			s[i] = 1 - s[i]
	}

	# Return the same argument
	return(s)
}



s.cond.alt = function(y, phi, mu, gamma, sigma, tau, k, s)
#
#	s ~ p(s | y, phi, mu, gamma, sigma, tau, k, s)
#
# This is an alternative (completely new) attempt at a conditional distribution
# function for the Markov chain, s. Rather than make piecemeal modifications of
# the previous chain, this function recomputes the entire chain from scratch. 
# The basic intuition is the same as s.cond in that the probability of being in
# any state at some time is determined by its effect on neighbouring states
# according to the order of the AR process. It differs in that it explores all
# possible future paths in the Markov chain, rather than those given by the
# previous iteration of the chain. This means that for a time series of length
# n whith m states and an order of r, the complexity is n*m^r ~ O(2^r)
{
	# y     : complete time series (vector)
	# phi	: auto-regression coefficients (vector)
	# mu    : state 0 mean
	# gamma : state 1 added mean
	# sigma : state 0 variance
	# tau   : state 1 added variance
	# k     : Markov state probabilities (vector)

	# Recursively search the probability space
	# This is a highly complex calculation
	p.est = function(i, s, d)
	{
		# The last state
		S = tail(s, n=1)
		# Its Markov probability
		K = k[1+S]
		# Recursion finished?
		if (d == 0) return(K)
		# Go forward, work backward
		P0 = p.est(i+1, c(s, 0), d-1)
		P1 = p.est(i+1, c(s, 1), d-1)
		# Calculation boundary
		r = min(length(phi), i-1)
		# Predict this y in the AR series
		mu.hat = mu + gamma*s[(i-r):(i-1)]
		y.hat = sum(phi[r:1]*(y[(i-r):(i-1)] - mu.hat))
		# Likelihood of y[j] given each state
		L0 = P0*dnorm(y[i], y.hat+mu, sqrt(sigma))
		L1 = P1*dnorm(y[i], y.hat+mu+gamma, sqrt(sigma+tau))
		# Probability that we remain in S
		if (S)
			theta = K*L1/(K*L1 + (1-K)*L0) # state 1
		else
			theta = K*L0/(K*L0 + (1-K)*L1) # state 0
		# Done!
		return(theta)
	}

	# Simulate s[i] from previous states
	s.sim = function(i, s)
	{
		# The last state
		S = tail(s, n=1)
		# Calculation boundary
		r = min(length(phi), length(y)-i)
		# Find the probability that we remain in the same state
		theta = p.est(i, s, r)
		# State transition is a Bernoulli random variable on theta
		remain = rbinom(1, 1, theta)
		# Either remain in this state or switch
		if (remain)
			return(S) # Remain in state S
		else
			return(1-S) # Switch to state 1-S
	}

	# On the first state, just the likelihood
	L0 = dnorm(y[1], mu, sqrt(sigma))
	L1 = dnorm(y[1], mu+gamma, sqrt(sigma+tau))
	# Simulate the first state
	s = rbinom(1, 1, L1/(L0 + L1))
	# Now do the rest of them
	for (i in 2:length(y))
	{
		ss = s.sim(i, s)
		s = c(s, ss)
	}
	return(s)
}



sigma.cond = function(y, phi, mu, gamma, omega, s)
#
#	sigma ~ p(sigma | y, phi, mu, gamma, omega, s)
#
# Generate the state 0 variance given other information about the series. We
# remove the mean first, then remove the effect of the previous terms of the AR
# model. Finally we take out the state 1 variance. What remains are IID random
# variables. The inverse gamma is used as the posterior distribution. 
{
	# y     : complete time series (vector)
	# phi   : auto-regression coefficients (vector)
	# mu    : state 0 mean
	# gamma : state 1 added mean
	# omega : tau/sigma
	# s     : Markov chain (vector)

	n = length(y)
	# Take out the mean
	y.star = y - mu - gamma*s
	# Take out the auto-regression component
	for (j in n:2)
	{
	 # We work back to front
	 r = min(length(phi), j-1)
	 # Subtract the previous values in the AR(p) series
	 y.star[j] = y.star[j] - sum(phi[1:r]*y.star[(j-1):(j-r)])
	}
	# Take out the state 1 variance
	y.star = y.star/sqrt(1 + omega*s)
	# Sum of squares
	y.sum = sum(y.star^2)
	# Simulate a new sigma
	1/rgamma(1, (1 + n)/2, (1 + y.sum)/2)
}



omega.cond = function(y, phi, mu, gamma, sigma, s)
#
#	omega ~ p(omega | y, phi, mu, gamma, sigma, s)
#
# Generate the state 1 variance given other information about the series. We
# remove the mean first, then remove the effect of the previous terms of the AR
# model. Finally we take out the state 0 variance. We can only simulate from
# the data points in state 1, so we truncate. What remains are IID random
# variables. The inverse-gamma is used as the posterior distribution. 
{
	# y     : complete time series (vector)
	# phi   : auto-regression coefficients (vector)
	# mu    : state 0 mean
	# gamma : state 1 added mean
	# sigma : state 0 variance
	# s     : Markov chain (vector)

	n = length(y)
	# Take out the mean
	y.star = y - mu - gamma*s
	# Take out the autoregression component
	for (j in n:2)
	{
	 # We work back to front
	 r = min(length(phi), j-1)
	 # Subtract the previous values
	 y.star[j] = y.star[j] - sum(phi[1:r]*y.star[(j-1):(j-r)])
	}
	# Only take state 1 data points & take out state 0 variance
	y.star = y.star[which(s == 1)]/sqrt(sigma)
	# Sum of squares
	y.sum = sum(y.star^2)
	# Simulate a new omega
	m = length(y.star)
	1/rgamma(1, (1 + m)/2, (1 + y.sum)/2)
}



phi.cond = function(y, mu, gamma, sigma, tau, s, p)
#
#	phi ~ p(phi | y, mu, gamma, sigma, tau, s)
#
# Simulate the (common) coefficients of the AR(p) processes which generated the
# time series y given the order and the other parameters. We rely on the method
# of Yule-Walker to estimate phi from the sample auto-covariance matrix. We also
# rely upon the asymptotic behaviour of this estimate for the distribution of
# phi. The MASS library was imported above for the "mvrnorm" function.
{
	# y     : complete time series (vector)
	# mu    : state 0 mean
	# gamma : state 1 added mean
	# sigma : state 0 variance
	# tau   : state 1 added variance
	# s     : Markov chain (vector)
	# p     : order of the AR processes

	# Take out the mean and variance
	y.star = (y - mu - gamma*s)/sqrt(sigma + tau*s)
	# Find the auto-covariances of the time series
	g = acf(y.star, type='cov', lag.max=p+1, plot=F)$acf
	# Build the auto-covariance matrix
	G = matrix(nrow=p, ncol=p)
	for (i in 1:p) for (j in 1:p) G[i,j] = g[abs(i-j) + 1]
	# Yule-Walker estimation
	G.inv = solve(G)
	phi = G.inv %*% g[1:p + 1]
	# Simulate from the mutlivariate normal
	n = length(y)
	mvrnorm(mu=phi, Sigma=(1/n)*G.inv)
}



k.cond = function(s)
#
#	k ~ p(k | s)
#
# Simulate the Markov kernel given only the Markov chain. The random component
# is modeled by the beta distribution with parameters given by counting the 
# state transitions in s.  
{
	# Transition counting matrix
	K = matrix(1, nrow=2, ncol=2)
	# Count the transitions
	for (j in 2:length(s))
	{
	 i = j-1 # previous time-point
	 u = s[i]+1 # states 0,1 go into cells 1,2 of the matrix respectively
	 w = s[j]+1 # ditto
	 K[u, w] = 1+K[u, w] # increment
	}
	# Simulate the probability of remaining in current state
	a = rbeta(1, K[1,1], K[1,2])
	b = rbeta(1, K[2,2], K[2,1])
	# Return these as a vector
	c(a, b)
}



mu.cond = function(y, gamma, s)
#
#	mu ~ p(mu | y, gamma, s)
#
# Simulate the state 0 mean which is actually common to both states. This also
# is independent of most other parameters. We only need gamma and s to remove
# the state 1 mean. The usual estimate of the time series mean is taken and
# its asymptotic behaviour  used as the distribution model for mu. The variance
# of this estimate is a sum of the auto-covariances decaying by lag. 
{
	# Take out the state 1 mean
	y.star = y - gamma*s
	# Estimate the state 0 mean
	y.bar = mean(y.star)
	# Find the auto-covariances
	g = acf(y.star, type='cov', plot=F)$acf
	n = length(g)
	# Variance of the sample mean
	nu = g[1] + 2*sum(g[2:n]*(1 - (2:n)/n))
	# Simulate using ordinary normal
	rnorm(1, y.bar, sqrt(nu/n))
}



gamma.cond = function(y, mu, s)
#
#	gamma ~ p(gamma | y, mu, s)
#
# Simulate the state 1 mean which is added to the state 0 mean. As above, it is
# independent of other parameters. We need only mu and s to remove the state 0
# mean. Unlike above, the estimated state 1 mean is removed from corresponding
# data points in the series so that y* is stationary. This allows us to get an
# accurate auto-covariance and, hence, an accurate sample variance for the
# asympototic distribution of the estimate used for gamma.
{
	# Take out the state 0 mean
	y.star = y - mu
	# Estimate the state 1 mean
	if (sum(s) > 0)
		y.bar = mean(y.star[which(s == 1)])
	else
		y.bar = 0
	# Take out the estimated mean too
	y.star = y.star - y.bar*s
	# Find the auto-covariances
	g = acf(y.star, type='cov', plot=F)$acf
	n = length(g)
	# Variance of the sample mean
	nu = g[1] + 2*sum(g[2:n]*(1 - (2:n)/n))
	# Simulate using ordinary normal
	rnorm(1, y.bar, sqrt(nu/n))
}



gibbs.sampler = function(y, phi, mu, gamma, sigma, tau, k, s, n)
#
# Performs n iterations of the Gibbs algorithm which generates n sample points
# from the unknown joint distribution of the parameter space. Convergence is
# not guaranteed but is strongly implicated by the output. 
{
	# Store the sample points here
	x = matrix(nrow=n, ncol=length(phi)+6)
	# Show a progress bar
	bar = progress.bar(title='Gibbs Sampler Progress', min=0, max=n)
	# Run, spot, run!
	for (i in 1:n)
	{
		# Indicate to the user how we are progressing
		set.progress.bar(bar, i, label=sprintf('%.0f%%', 100*i/n))
		# The real work of the program is done in these lines
		phi = phi.cond(y, mu, gamma, sigma, tau, s, length(phi))
		mu = mu.cond(y, gamma, s)
		gamma = gamma.cond(y, mu, s)
		omega = tau/sigma
		sigma = sigma.cond(y, phi, mu, gamma, omega, s)
		omega = omega.cond(y, phi, mu, gamma, sigma, s)
		tau = sigma*(omega - 1) # forcing tau > 0 creates bias
		s = s.cond(y, phi, mu, gamma, sigma, tau, k, s)
		k = k.cond(s)
		# Insert sample points into matrix rows
		x[i,] = c(phi, mu, gamma, sigma, tau, k)
	}
	close(bar)
	# Phi is a vector; each part has its own column
	phi.names = paste('phi', 1:length(phi), sep='.')
	# Name the matrix columns according to the parameter they represent
	colnames(x) = c(phi.names, 'mu', 'gamma', 'sigma', 'tau', 'k.0', 'k.1')
	# Voila
	return(x)
}



gibbs.boot = function(y, p, n)
#
# Calculates sane starting values to give to the Gibbs sampler by treating the
# time series data as coming from a bimodal distribution. The mixtools package
# implements the EM algorithm to estimate the distributions in the mixture. We
# draw on these to get a first approximation of the means and variances of the
# AR processes corresponding to the two states. 
{
	# y : complete time series (vector)
	# p : order of the AR processes (vector)
	# n : the number of iterations to run

	cat('Bootstrapping with EM algorithm\n')
	# Treat y as a mixture
	y.mix = normalmixEM(y)
	# Assume that state 0 has the lower variance
	if (y.mix$sigma[1] < y.mix$sigma[2]) # This might change!
	{
		mu = y.mix$mu[1]
		gamma = y.mix$mu[2] - mu
		sigma = y.mix$sigma[1]^2
		tau = y.mix$sigma[2]^2 - sigma
	}
	else
	{
		mu = y.mix$mu[2]
		gamma = y.mix$mu[1] - mu
		sigma = y.mix$sigma[2]^2
		tau = y.mix$sigma[1]^2 - sigma
	}
	# Now take a guess at s and k
	s = NULL
	K = matrix(0, nrow=2, ncol=2) # count state transitions
	# Guess a Markov chain
	for (i in 1:length(y))
	{
		# Ignore the AR effects for now
		L0 = dnorm(y[i], mu, sqrt(sigma))
		L1 = dnorm(y[i], mu+gamma, sqrt(sigma+tau))
		# By greater likelihood
		if (L0 > L1)
		{
			s = c(s, 0)
			# Count the state transition
			if (i > 1) K[1+s[i-1], 1+s[i]] = 1+K[1+s[i-1], 1+s[i]]
		}
		else
		{
			s = c(s, 1)
			# Count the state transition
			if (i > 1) K[1+s[i-1], 1+s[i]] = 1+K[1+s[i-1], 1+s[i]]
		}
	}
	# Markov kernel
	k = c(0, 0)
	# Transform counts into frequencies
	k[1] = K[1,1] / (K[1,1] + K[1,2])
	k[2] = K[2,2] / (K[2,2] + K[2,1])
	# Estimate phi using Yule-Walker algorithm
	g = acf((y - mu - gamma*s)/sqrt(sigma + tau*s), type='cov', plot=F)$acf
	G = matrix(nrow=p, ncol=p)
	for (i in 1:p) for (j in 1:p) G[i,j] = g[abs(i-j) + 1]
	G.inv = solve(G)
	phi = G.inv %*% g[1:p + 1]
	# Cleanup temporary values
	rm(y.mix, K, g, G, G.inv)
	# Report what we are using
	cat('Booting with parameters\n')
	cat('\tphi\t', phi, '\n')
	cat('\tmu\t', mu, '\n')
	cat('\tgamma\t', gamma, '\n')
	cat('\tsigma\t', sigma, '\n')
	cat('\ttau\t', tau, '\n')
	cat('\tk\t', k, '\n')
	cat('number of iterations=', n, '\n')
	# Ready to go
	gibbs.sampler(y, phi, mu, gamma, sigma, tau, k, s, n)
}



try.gibbs.and.save = function(y, p, n, path)
#
# An emergent bug in the code that is difficult to isolate will sometimes cause
# the algorithm to terminate. In case this happens during a simulation study we
# can use this function to rerun it and to save the sample to file after it has
# been successfully obtained. We can leave the simulation running 
{
	x = NA
	quit = F
	while (!quit)
	{
		x = try(gibbs.boot(y$ts, p, n), silent=T)
		if (class(x) == 'try-error')
			cat(x)
		else
			quit=T
	}
	save(list=c('x', 'y'), file=path)
	return(x)
}



series.plot = function(y)
{
	par(mfrow=c(1,1))
	plot(y$ts, ylab='Data', main='Simulation')
	abline(h=y$mu, col='blue')
	abline(h=y$mu+y$gamma, col='red')
}



gibbs.plot = function(x, y)
{
	# We want to plot state 1 mean, variance rather than gamma, tau

	# Store gamma and tau
	gamma = x[,'gamma']
	tau = x[,'tau']
	# Add to get state 1 estimates
	x[,'gamma'] = x[,'mu'] + gamma
	x[,'tau'] = x[,'sigma'] + tau
	# Also for the true parameters
	y.gamma = y$mu + y$gamma
	y.tau = y$sigma + y$tau
	# Pull estimates out of the matrix
	#x.mean = apply(x[-(1:burn),], 2, mean)

	# Custom plotting function (with default arguments) 

	my.col = function(col) {
		adjustcolor(col, alpha=0.2)
	}
	my.plot = function(a, lim, lab) {
		col = my.col('blue')
		ts.plot(x[,a], ylim=lim, xlab='Iteration', ylab=lab, col=col)
	}
	my.lines = function(b, col='red') {
		lines(x[,b], col=my.col(col))
	}
	sim.line = function(sim, col) {
		abline(h=sim, lty=2, col=col)
	}
	est.line = function(est, col) {
		abline(h=x.mean[est], lty=3, col=col)
	}

	# AR order
	p = ncol(x) - 6
	# Setup multiplot
	par(mfrow=c(2,2))

	# AR coefficients

	r = range(c(x[,1:p]))
	my.plot('phi.1', r, 'AR')
	if (p > 1)
	{
		fg = c('red', 'green', 'orange')
		bg = c('pink', 'palegreen', 'orange4')

		for (i in 2:p)
			my.lines(paste('phi', i, sep='.'), fg[i-1])
		for (i in 2:p)
			sim.line(y$phi[i], fg[i-1])
		#for (i in 2:p)
			#est.line(paste('phi', i, sep='.'), fg[i-1])
	}
	sim.line(y$phi[1], 'blue')
	#est.line('phi.1', 'blue')

	# Means

	r = range(c(x[,c('mu', 'gamma')]))
	my.plot('mu', r, 'Means')
	my.lines('gamma')
	sim.line(y$mu, 'blue')
	sim.line(y.gamma, 'red')
	#est.line('mu', 'blue')
	#est.line('gamma', 'red')

	# Variances

	r = range(c(x[,c('sigma', 'tau')]))
	my.plot('sigma', r, 'Variances')
	my.lines('tau')
	sim.line(y$sigma, 'blue')
	sim.line(y.tau, 'red')
	#est.line('sigma', 'blue')
	#est.line('tau', 'red')

	# Markov Kernel

	r = range(c(x[,c('k.0', 'k.1')]))
	my.plot('k.0', r, 'Kernel')
	my.lines('k.1')
	sim.line(y$k[1], 'blue')
	sim.line(y$k[2], 'red')
	#est.line('k.0', 'blue')
	#est.line('k.1', 'red')

	# Restore gamma, tau
	x[,'gamma'] = gamma
	x[,'tau'] = tau
}


