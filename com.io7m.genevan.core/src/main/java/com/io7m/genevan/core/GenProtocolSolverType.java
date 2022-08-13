/*
 * Copyright © 2022 Mark Raynsford <code@io7m.com> https://www.io7m.com
 *
 * Permission to use, copy, modify, and/or distribute this software for any
 * purpose with or without fee is hereby granted, provided that the above
 * copyright notice and this permission notice appear in all copies.
 *
 * THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 * WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY
 * SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 * WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 * ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF OR
 * IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 */


package com.io7m.genevan.core;

import java.util.Collection;
import java.util.List;

/**
 * The type of protocol solvers.
 */

public interface GenProtocolSolverType
{
  /**
   * Pick the "best" possible handler for the given set of server protocols and
   * client handlers.
   *
   * @param serverProvides  The versions supported by the server
   * @param clientSupports  The protocol versions supported by the client
   * @param preferProtocols The protocol names to prefer in the case of
   *                        ambiguity
   *
   * @return The best possible handler
   *
   * @throws GenProtocolException On errors
   */

  GenProtocolSolved solve(
    Collection<? extends GenProtocolServerEndpointType> serverProvides,
    Collection<? extends GenProtocolClientHandlerType> clientSupports,
    List<String> preferProtocols)
    throws GenProtocolException;
}
